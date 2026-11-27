------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-|
Ground values ("Lidar.Ground") as static data in Lean's format, as Lean's @emitGroundDecl@ writes
them: constructor objects, strings and closures with reference count 0, which the runtime never
counts or frees, and no initialiser. A value is a C global that points to its object, or holds
its scalar.

Calls of @Name.mkStr@, @Name.str@ and @Name.num@ are folded into the constructor objects of the
names, with the hashes that Lean computes (@Name.hash@), and the conversions of literals to
scalars (@UInt32.ofNat@) into the scalars.
-}
module Lidar.Lean.CGen.Ground( foldable, groundDecls, closureInit, cString ) where

import Control.Monad( foldM )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Bits( shiftL, shiftR, xor, (.&.) )
import Data.Char( ord, isPrint )
import Data.List( intercalate )
import Data.Word( Word64 )
import Numeric( showOct )
import Lidar
import Lidar.Env( Env(..), M, runM, liftE, ask, gets, modify )
import Lidar.Query( Gamma, inferV )
import Lidar.Layout( leaves )
import Lidar.Ground
import Lidar.Lean.Decls( leanName, rawOfNat )
import Lidar.Lean.CGen.Layout

------------------------------------------------------------------------------
-- Folded calls
------------------------------------------------------------------------------

-- | The functions whose calls with ground arguments are folded at compile time.
foldable :: Name -> Bool
foldable f = S.member f (S.fromList (M.keys ofNats ++ mkStrs ++ [nameStr, nameNum]))

-- the conversions of literals to scalars (`Decls.rawOfNat`)
ofNats :: M.Map Name Raw
ofNats = M.fromList [(leanName f, r) | r <- [RInt (IntType Unsigned w) | w <- [W8, W16, W32, W64, WSize]], Just f <- [rawOfNat r]]

mkStrs :: [Name]
mkStrs = [leanName ("Lean.Name.mkStr" ++ show i) | i <- [1..8 :: Int]]

nameStr, nameNum :: Name
nameStr = leanName "Lean.Name.str._override"
nameNum = leanName "Lean.Name.num._override"

-- the hash of `Name.anonymous`, and Lean's `mixHash` (`lean_uint64_mix_hash`)
anonymousHash :: Word64
anonymousHash = 1723

mixHash :: Word64 -> Word64 -> Word64
mixHash h k0 = (h `xor` k3) * murmurM
  where k1 = k0 * murmurM
        k2 = k1 `xor` (k1 `shiftR` 47)
        k3 = k2 `xor` murmurM

murmurM :: Word64
murmurM = 0xc6a4a7935bd1e995

-- Lean's `String.hash` (`lean_string_hash`): MurmurHash64A of the UTF-8 bytes, with seed 11
stringHash :: String -> Word64
stringHash s = final (foldl tailByte (foldl block h0 blocks) (zip [0..] rest))
  where
    bytes = map fromIntegral (concatMap utf8 s) :: [Word64]
    len = length bytes
    h0 = 11 `xor` (fromIntegral len * murmurM)
    (blocks,rest) = (chunks (take (len - len `mod` 8) bytes), drop (len - len `mod` 8) bytes)
    chunks [] = []
    chunks bs = let (c,cs) = splitAt 8 bs in c : chunks cs
    le bs = sum [b `shiftL` (8*i) | (i,b) <- zip [0..] bs]
    block h c = let k1 = le c * murmurM
                    k2 = (k1 `xor` (k1 `shiftR` 47)) * murmurM
                in (h `xor` k2) * murmurM
    tailByte h (i,b) = h `xor` (b `shiftL` (8*i))
    final h = let h1 = if null rest then h else h * murmurM
                  h2 = (h1 `xor` (h1 `shiftR` 47)) * murmurM
              in h2 `xor` (h2 `shiftR` 47)

------------------------------------------------------------------------------
-- Static values
------------------------------------------------------------------------------

-- | A leaf of a static value: a constant object pointer, or a scalar by its bits.
data GLeaf = GObj String | GScalar Integer

-- | A static value: its leaves, and the string or the hash of the name that it is, if any.
data Val = Val{ valLeaves :: [GLeaf], valStr :: Maybe String, valHash :: Maybe Word64 }

leavesOnly :: [GLeaf] -> Val
leavesOnly ls = Val ls Nothing Nothing

-- `cxFun`: the C name of a function, for a closure
data Ctx = Ctx{ cxEnv :: Env, cxFun :: Name -> Maybe String, cxBase :: String }

-- the declarations written so far (last first), the next number of an object, the values of the
-- globals and of the bindings of the current value, and the types of the bindings
data St = St{ stDecls :: [String], stNext :: Int, stGlobals :: M.Map Name Val
            , stLocals :: M.Map Path Val, stGamma :: Gamma }

type G a = M Ctx St a

-- | The static objects of the ground values of a lowered program that can be written statically
-- (each before the objects that point to it), and the prototype and the definition of each of
-- these values, given the C names of functions (for closures) and of values, and the values
-- that are local to the module (static). A value that cannot be written, or that refers to one
-- that cannot, is initialised as before.
groundDecls :: Env -> (Name -> Maybe String) -> M.Map Name String -> (Name -> Bool) -> Program -> ([String], M.Map Name (String,String))
groundDecls env funName cnames local prog = go (groundOrder grounds) (St [] 0 M.empty M.empty M.empty) M.empty
  where
    grounds = groundValues foldable prog
    types = M.fromList [(x,t) | DefVal x _ _ t _ <- progDefs prog]
    go [] st protos = (reverse (stDecls st), protos)
    go (x:xs) st protos
      = case M.lookup x cnames of
          Just cname | Right ((rt,c),st') <- runM (writeValue x (types M.! x) (grounds M.! x)) (Ctx env funName cname) st
            -> let decl = (if local x then "static " else "LEAN_EXPORT ") ++ rt ++ " " ++ cname
               in go xs st' (M.insert x (decl ++ ";", decl ++ " = " ++ c ++ ";") protos)
          _ -> go xs st protos

-- the C type and the initialiser of a ground value
writeValue :: Name -> VType -> Ground -> G (String,String)
writeValue x t (Ground binds res)
  = do modify (\st -> st{ stNext = 0, stLocals = M.empty, stGamma = M.empty })
       mapM_ bind binds
       v <- genVal res
       ls <- liftE (mapM leafOf (leaves t))
       modify (\st -> st{ stGlobals = M.insert x v (stGlobals st) })
       case (ls, valLeaves v) of
         ([l],[g]) -> return (cType l, leafC g)
         ([],[]) -> return ("lean_object*", tagged 0)
         _ -> fail "a value with several leaves"
  where
    bind (y,ty,b) = do v <- case b of
                              GValue w -> genVal w
                              GCall f _ vs -> foldCall ty f vs
                              GGlob g _ -> gets (M.lookup g . stGlobals) >>= maybe (fail ("not static: " ++ show g)) return
                       modify (\st -> st{ stLocals = M.insert y v (stLocals st), stGamma = M.insert y (V ty) (stGamma st) })

leafC :: GLeaf -> String
leafC g = case g of
            GObj e -> e
            GScalar n -> show n

-- `lean_box(n)` as a constant expression
tagged :: Integer -> String
tagged n = "((lean_object*)(((size_t)(" ++ show n ++ ") << 1) | 1))"

genVal :: VVal -> G Val
genVal val
  = case val of
      Var x -> do v <- gets (M.lookup x . stLocals)
                  maybe (fail ("unbound " ++ show x)) return v
      UnitV -> return (leavesOnly [])
      Lit (LitSmallInt n) | n >= 0 -> return (leavesOnly [GObj (tagged n)])
      Lit (LitInt _ n) | n >= 0 -> return (leavesOnly [GScalar n])
      Lit (LitChar c) -> return (leavesOnly [GScalar (toInteger (ord c))])
      Inj i t UnitV | Right (LScalar _) <- leafOf t -> return (leavesOnly [GScalar (toInteger i)])
      Tuple vs -> leavesOnly . concatMap valLeaves <$> mapM genVal vs
      Ptr _ (Constant (ConstString s)) -> do o <- stringObject s
                                             return (Val [GObj o] (Just s) Nothing)
      Ptr _ a -> do o <- genObj 0 a
                    return (leavesOnly [GObj o])
      TyApp v _ -> genVal v
      Up v -> genVal v
      Some v -> genVal v
      Pack _ _ v -> genVal v
      _ -> fail ("not a static value: " ++ show val)

-- an object with the tag of the alternative that it is an injection into
genObj :: Int -> AVal -> G String
genObj tag val
  = case val of
      UnitA -> return (tagged (toInteger tag))
      Roll _ v -> genObj tag v
      InjA i _ v -> genObj i v
      Box v -> do env <- cxEnv <$> ask
                  g <- gets stGamma
                  t <- liftE (inferV env g v)
                  ls <- liftE (mapM leafOf (leaves t))
                  fs <- genVal v
                  ctorObject tag ls (valLeaves fs)
      Fun f -> closureObject f
      _ -> fail ("not a static object: " ++ show val)

-- a new static object of a C type with an initialiser, as a constant `lean_object*`
object :: String -> String -> G String
object ctype body
  = do base <- cxBase <$> ask
       n <- gets stNext
       let name = base ++ "_value_" ++ show n
       modify (\st -> st{ stNext = n + 1, stDecls = ("static const " ++ ctype ++ " " ++ name ++ " = " ++ body ++ ";") : stDecls st })
       return ("((lean_object*)&" ++ name ++ ")")

header :: String -> Int -> Int -> String
header size other tag = "{.m_rc = 0, .m_cs_sz = " ++ size ++ ", .m_other = " ++ show other ++ ", .m_tag = " ++ show tag ++ "}"

-- A constructor object: its objects, `usize` fields and other scalars in the slots of
-- `CGen.Layout.payload`, the scalars as bytes in words of 8 (`LEAN_SCALAR_PTR_LITERAL`), and its
-- spill objects, which are written first.
ctorObject :: Int -> [Leaf] -> [GLeaf] -> G String
ctorObject tag ls gs
  = do pl <- liftE (payload ls)
       if length gs /= length ls then fail "a constructor object with the wrong number of fields" else do
         fields <- mapM slot (zip (plSlots pl) gs)
         let spilled = M.fromList [(di,e) | Left (Left (Right di,e)) <- fields]
             spill d n link = object "lean_ctor_object"
                                ("{.m_header = " ++ header ("sizeof(lean_ctor_object) + sizeof(void*)*" ++ show n) n 0
                                 ++ ", .m_objs = {" ++ intercalate "," ([spilled M.! (d,i) | i <- [0 .. n - 1 - length link]] ++ link) ++ "}}")
         links <- foldM (\link (d,n) -> (:[]) <$> spill d n link) [] (reverse (zip [1..] (plSpills pl)))
         let objs = M.fromList ([(i,e) | Left (Left (Left i,e)) <- fields] ++ [(plObjs pl - 1, l) | l <- links])
             usizes = M.fromList [(i,n) | Left (Right (i,n)) <- fields]
             bytes = M.fromList (concat [b | Right b <- fields])
             ssize = ((plScalars pl + 7) `div` 8) * 8
             byteAt i = M.findWithDefault 0 i bytes
             words8 = [ "LEAN_SCALAR_PTR_LITERAL(" ++ intercalate ", " [show (byteAt (w*8 + j)) | j <- [0..7]] ++ ")" | w <- [0 .. ssize `div` 8 - 1] ]
             size = "sizeof(lean_ctor_object) + sizeof(void*)*" ++ show (plObjs pl) ++ " + sizeof(size_t)*" ++ show (plUSize pl) ++ " + " ++ show ssize
             fs = [objs M.! i | i <- [0 .. plObjs pl - 1]]
                  ++ ["(lean_object*)(size_t)(" ++ show (usizes M.! i) ++ "ULL)" | i <- [0 .. plUSize pl - 1]]
                  ++ words8
         object "lean_ctor_object" ("{.m_header = " ++ header size (plObjs pl) tag ++ ", .m_objs = {" ++ intercalate "," fs ++ "}}")
  where
    slot (s,g) = case (s,g) of
                   (SObj i, GObj e) -> return (Left (Left (Left i,e)))
                   (SSpill d i, GObj e) -> return (Left (Left (Right (d,i),e)))
                   (SUSize i, GScalar n) -> return (Left (Right (i,n)))
                   (SScalar r off, GScalar n) -> do k <- maybe (fail "a usize scalar") return (scalarSize r)
                                                    return (Right [(off + j, (n `shiftR` (8*j)) .&. 0xff) | j <- [0 .. k-1]])
                   _ -> fail "a field that does not match its slot"

-- a top-level function as a closure without arguments (as `CGen.genFun`)
closureObject :: Name -> G String
closureObject f
  = do cx <- ask
       case (M.lookup f (envSigs (cxEnv cx)), cxFun cx f) of
         (Just (SigFun _ ps _ r), Just cname) ->
           do pls <- liftE (mapM (mapM leafOf . leaves . snd) ps)
              rls <- liftE (mapM leafOf (leaves r))
              if all (== [LObj]) (rls : pls) && length ps <= 16
                then object "lean_closure_object" (closureInit cname (length ps))
                else fail ("the function " ++ show f ++ " as a closure")
         _ -> fail ("unknown function " ++ show f)

-- | The initialiser of a static closure object without arguments, given its C function and
-- its arity.
closureInit :: String -> Int -> String
closureInit fn arity
  = "{.m_header = " ++ header "sizeof(lean_closure_object)" 0 245 ++ ", .m_fun = (void*)" ++ fn
    ++ ", .m_arity = " ++ show arity ++ ", .m_num_fixed = 0, .m_objs = {}}"

stringObject :: String -> G String
stringObject s
  = let (lit,size,len) = cString s
    in object "lean_string_object" ("{.m_header = " ++ header "0" 0 249 ++ ", .m_size = " ++ show (size + 1) ++ ", .m_capacity = "
                                    ++ show (size + 1) ++ ", .m_length = " ++ show len ++ ", .m_data = " ++ lit ++ "}")

-- A folded call: the conversion of a literal to a scalar, or the constructor of a name, whose
-- object holds its prefix, its last component and its hash.
foldCall :: VType -> Name -> [VVal] -> G Val
foldCall t f vs
  | Just _ <- M.lookup f ofNats, [v] <- vs, Just n <- intValue v, VRaw r <- t
  = return (leavesOnly [GScalar (n `mod` (2 ^ (8 * maybe 8 id (scalarSize r))))])
  | f `elem` mkStrs
  = do ss <- mapM genVal vs
       foldl (\acc s -> acc >>= \p -> strName p s) (return anonymous) ss
  | f == nameStr, [p,s] <- vs
  = do pv <- genVal p
       sv <- genVal s
       strName pv sv
  | f == nameNum, [p, v] <- vs, Just n <- intValue v
  = do pv <- genVal p
       h <- prefixHash pv
       name 2 pv (GObj (tagged n)) (mixHash h (if n < 2^(64 :: Int) then fromInteger n else 17))
  | otherwise = fail ("cannot fold " ++ show f)
  where
    anonymous = Val [GObj (tagged 0)] Nothing (Just anonymousHash)
    -- the only name without an object is `anonymous`
    prefixHash pv = case (valHash pv, valLeaves pv) of
                      (Just h, _) -> return h
                      (_, [GObj e]) | e == tagged 0 -> return anonymousHash
                      _ -> fail "a name prefix that is not static"
    strName pv sv
      = do h <- prefixHash pv
           case (valStr sv, valLeaves sv) of
             (Just s, [g]) -> name 1 pv g (mixHash h (stringHash s))
             _ -> fail "a name component that is not static"
    name tag pv g h
      = case valLeaves pv of
          [p] -> do o <- ctorObject tag [LObj, LObj, LScalar (RInt (IntType Unsigned W64))] [p, g, GScalar (toInteger h)]
                    return (Val [GObj o] Nothing (Just h))
          _ -> fail "a name prefix that is not an object"

------------------------------------------------------------------------------
-- C strings
------------------------------------------------------------------------------

-- | The C literal of the UTF-8 bytes of a string, their number, and the number of characters.
cString :: String -> (String,Int,Int)
cString s = ("\"" ++ concatMap esc bytes ++ "\"", length bytes, length s)
  where
    bytes = concatMap utf8 s
    esc b | b == ord '"' || b == ord '\\' = ['\\', toEnum b]
          | b == ord '?' = "\\?"   -- no trigraphs
          | b < 128 && isPrint (toEnum b) = [toEnum b]
          | otherwise = "\\" ++ pad (showOct b "")   -- octal escapes take at most three digits
    pad o = replicate (3 - length o) '0' ++ o

utf8 :: Char -> [Int]
utf8 c
  | n < 0x80 = [n]
  | n < 0x800 = [0xC0 + shiftR n 6, cont 0]
  | n < 0x10000 = [0xE0 + shiftR n 12, cont 6, cont 0]
  | otherwise = [0xF0 + shiftR n 18, cont 12, cont 6, cont 0]
  where
    n = ord c
    cont k = 0x80 + (shiftR n k .&. 0x3F)
