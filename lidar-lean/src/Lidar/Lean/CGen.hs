------------------------------------------------------------------------------
-- Copyright 2026, Anton Lorenzen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-|
C generation against Lean's runtime (@lean.h@) from lowered IR.

Values are represented as "Lidar.Lean.CGen.Layout" describes: every binder of the IR is a C
local per leaf of its type, named after its path. Boxes are constructor objects (built with
@lean_alloc_ctor@, or in the block of a credit), unit alternatives are @lean_box(i)@, closures
are Lean's closures, which take and return objects, and reference counting is @lean_inc@ and
@lean_dec@. Join points are labels, as in Koka's C generator.

The C file follows Lean's ABI, so that it links with modules that Lean compiled: functions keep
their C names (from the dump), parameters of type @𝟙@ (Lean's @lcVoid@) have no C parameter,
and a call of a function of another module converts its arguments and result to the impure
signature of the callee, dropping the erased arguments of an external C function as Lean does.
The module's initializers and the C @main@ are the ones Lean's @EmitC@ writes.
-}
module Lidar.Lean.CGen( cgenModule ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Bits( shiftR, (.&.) )
import Data.Functor.Const( Const(..) )
import Data.Char( ord, isAlphaNum, isAscii, isPrint )
import Data.List( intercalate )
import Data.Maybe( fromMaybe, mapMaybe )
import Control.Monad( forM, zipWithM )
import Numeric( showHex, showOct )
import Prettyprinter( Doc, pretty, vsep, hsep, nest, hardline, (<+>), layoutPretty, LayoutOptions(..), PageWidth(..) )
import Prettyprinter.Render.String( renderString )
import Lidar
import Lidar.Env( Env(..), envOf, dataBody, boxContents, M, runM, liftE, state, modify, get, put )
import Lidar.Query( Gamma, inferV, inferVar, altTypes, unboxRuGamma, copyRuGamma, uniqueGamma )
import Lidar.Traversal( child, boxTag, fvA, descendA, descendV, descendE )
import Lidar.Layout( leaves, shapeIsHeap )
import qualified Lidar.Lean.Dump as D
import Lidar.Lean.Decls( leanName, rawOfNat )
import Lidar.Lean.CGen.Layout

type C = Doc ()

------------------------------------------------------------------------------
-- Targets: how a function or value is reached from C
------------------------------------------------------------------------------

data Call = Direct      -- ^ a C function or global of that name
          | Standard    -- ^ a C function of the runtime, without the erased arguments
          | Pattern     -- ^ an inline pattern of an @\@[extern]@ entry, with @#i@ for argument i

-- | The C name or pattern of a function or value, and its impure signature (parameters and
-- result) if it is not of this module: calls convert to it.
data Target = Target{ tgtName :: String, tgtCall :: Call, tgtImpure :: Maybe ([D.Type],D.Type) }

-- the function or value that a link names, through its `@[extern]` entry for C if it has one
linkTarget :: Bool -> D.Link -> Target
linkTarget own l
  = case concatMap entry (fromMaybe [] (D.linkExtern l)) of
      (c,n):_ -> Target n c impure
      [] -> Target (D.linkCName l) Direct (if own then Nothing else impure)
  where
    impure = fmap (\(ps,r) -> (map D.paramType ps, r)) (D.linkImpure l)
    entry e = case e of
                D.Standard b f | b `elem` ["c","all"] -> [(Standard,f)]
                D.Inline b p | b `elem` ["c","all"] -> [(Pattern,p)]
                _ -> []

-- the functions of Lean's runtime that the elaboration calls by name (`Decls.builtinCtorSigs`
-- and the conversions of literals, `Decls.rawOfNat`)
runtimeFuns :: [(D.Name,String)]
runtimeFuns = [ ("Int.ofNat","lean_nat_to_int"), ("Int.negSucc","lean_int_neg_succ_of_nat")
              , ("UInt8.ofNat","lean_uint8_of_nat"), ("UInt16.ofNat","lean_uint16_of_nat")
              , ("UInt32.ofNat","lean_uint32_of_nat"), ("UInt64.ofNat","lean_uint64_of_nat")
              , ("USize.ofNat","lean_usize_of_nat") ]

-- the targets of the module's declarations, of the constants they use and of the runtime
targetsOf :: D.Dump -> M.Map Name Target
targetsOf d
  = M.fromList ([(leanName (D.declName x), linkTarget (isBody x) (D.declLink x)) | x <- D.dumpDecls d]
                ++ [(leanName (D.constName c), linkTarget False (D.constLink c)) | c <- D.dumpConsts d]
                ++ [(leanName n, Target f Standard Nothing) | (n,f) <- runtimeFuns])
  where isBody x = case D.declValue x of { D.Body _ -> True; D.Extern _ -> False }

-- the leaf of an impure type, or Nothing for `lcVoid`, which has no representation
impureLeaf :: D.Type -> Maybe Leaf
impureLeaf t
  = case t of
      D.TConst "lcVoid" -> Nothing
      D.TConst "UInt8" -> Just (LScalar RUInt8)
      D.TConst "UInt16" -> Just (LScalar RUInt16)
      D.TConst "UInt32" -> Just (LScalar RUInt32)
      D.TConst "UInt64" -> Just (LScalar RUInt64)
      D.TConst "USize" -> Just (LScalar RUSize)
      D.TConst "Float" -> Just (LScalar RFloat64)
      D.TConst "Float32" -> Just (LScalar RFloat32)
      _ -> Just LObj

isErased :: D.Type -> Bool
isErased t = t == D.TConst "lcErased"

-- a value of one representation as one of another
convert :: Leaf -> Leaf -> String -> String
convert from to e
  = case (from,to) of
      (LObj, LScalar r) -> unboxScalar r e
      (LScalar r, LObj) -> boxScalar r e
      _ -> e

------------------------------------------------------------------------------
-- The generation monad
------------------------------------------------------------------------------

-- the next fresh number, and the definitions of closures
data St = St{ stUniq :: Int, stLams :: [C] }

type G a = M () St a

-- `cxJoins`: the label and the parameters of each join point in scope, and whether it is
-- recursive (its jumps then assign the parameters in parallel)
data Ctx = Ctx{ cxEnv :: Env, cxTargets :: M.Map Name Target, cxGamma :: Gamma
              , cxJoins :: M.Map Name (String,[(Path,VType)],Bool) }

fresh :: String -> G String
fresh s = state (\st -> ("_" ++ s ++ show (stUniq st), st{ stUniq = stUniq st + 1 }))

liftQ :: Either String a -> G a
liftQ = liftE

bindVar :: Ctx -> Path -> Ty -> Ctx
bindVar cx x t = cx{ cxGamma = M.insert x t (cxGamma cx) }

tyOf :: Ctx -> VVal -> G VType
tyOf cx v = liftQ (inferV (cxEnv cx) (cxGamma cx) v)

tyOfName :: Ctx -> Path -> G Ty
tyOfName cx x = liftQ (inferVar (cxGamma cx) x)

leavesOf :: VType -> G [Leaf]
leavesOf t = liftQ (mapM leafOf (leaves t))

leavesOfTy :: Ty -> G [Leaf]
leavesOfTy (V t) = leavesOf t
leavesOfTy (A _) = return [LObj]

target :: Ctx -> Name -> G Target
target cx f = maybe (fail ("no C name for " ++ show f)) return (M.lookup f (cxTargets cx))

------------------------------------------------------------------------------
-- C syntax
------------------------------------------------------------------------------

text :: String -> C
text = pretty

-- a block with each statement on its own line
block :: [C] -> C
block ss = "{" <> nest 2 (mconcat [hardline <> s | s <- ss]) <> hardline <> "}"

-- a statement expression `({ s1; s2; e; })`
stmtExpr :: [String] -> String -> String
stmtExpr ss e = "({ " ++ concatMap (++ " ") ss ++ e ++ "; })"

call :: String -> [String] -> String
call f as = f ++ "(" ++ intercalate ", " as ++ ")"

ifElse :: String -> [C] -> [C] -> C
ifElse c s1 s2 = "if (" <> text c <> ")" <+> block s1 <+> "else" <+> block s2

-- the C local of a path: its root and steps, with alternatives and fields by index
localName :: Path -> String
localName (Path x ss) = "x_" ++ encode (show x) ++ concat ["_p_" ++ encode (step s) | s <- ss]
  where
    step s = case s of
               SInjA i _ -> "inj" ++ show i
               SInjV i _ -> "inj" ++ show i
               SField i _ -> "field" ++ show i
               _ -> show s

encode :: String -> String
encode = concatMap enc
  where
    enc c | isAlphaNum c && isAscii c = [c]
          | c == '_' = "__"
          | otherwise = "_x" ++ showHex (ord c) "_"

-- the C locals of the leaves of a path
leafNames :: Path -> Int -> [String]
leafNames x 1 = [localName x]
leafNames x n = [localName x ++ "_l" ++ show i | i <- [0..n-1]]

-- declare the leaves of a path, with their values
declare :: Path -> [Leaf] -> [String] -> [C]
declare x ls es = [text (cType l ++ " " ++ n ++ " = " ++ e ++ ";") | (l,n,e) <- zip3 ls (leafNames x (length ls)) es]

-- declare the leaves of a path without values
declareOnly :: Path -> [Leaf] -> [C]
declareOnly x ls = [text (cType l ++ " " ++ n ++ ";") | (l,n) <- zip ls (leafNames x (length ls))]

-- the C type of a result: its leaf, or an object (`lean_box(0)`) without leaves
resultType :: [Leaf] -> G String
resultType ls = case ls of
                  [l] -> return (cType l)
                  [] -> return "lean_object*"
                  _ -> fail "a result with several leaves"

------------------------------------------------------------------------------
-- Literals
------------------------------------------------------------------------------

-- as Lean's `emitLit`: `lean_cstr_to_nat` parses its string on every call
natLit :: Integer -> String
natLit n
  | n < 2^(32::Int) = "lean_unsigned_to_nat(" ++ show n ++ "u)"
  | n < 2^(64::Int) = "lean_uint64_to_nat(" ++ show n ++ "ULL)"
  | otherwise = "lean_cstr_to_nat(\"" ++ show n ++ "\")"

-- `lean_mk_string_unchecked` with the C literal of the UTF-8 bytes, their number and the
-- number of characters
strLit :: String -> String
strLit s = call "lean_mk_string_unchecked" ["\"" ++ concatMap esc bytes ++ "\"", show (length bytes), show (length s)]
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

genLit :: Lit -> G String
genLit lit
  = case lit of
      LitInt n | n >= 0 -> return (natLit n)
      LitString s -> return (strLit s)
      LitChar c -> return (show (ord c) ++ "u")
      _ -> fail ("literal " ++ show lit)

------------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------------

-- the leaves of a value
genV :: Ctx -> VVal -> G [String]
genV cx val
  = case val of
      Var x -> do ls <- tyOfName cx x >>= leavesOfTy
                  return (leafNames x (length ls))
      Glob x _ -> do ls <- tyOf cx val >>= leavesOf
                     tgt <- target cx x
                     return [tgtName tgt | _ <- ls]
      DupV v -> do es <- genV cx v
                   ls <- tyOf cx v >>= leavesOf
                   return [if l == LObj then call "lt_dup" [e] else e | (l,e) <- zip ls es]
      UnitV -> return []
      Lit lit -> (:[]) <$> genLit lit
      NoReuse _ _ -> return ["NULL"]
      TyApp v _ -> genV cx v
      Up v -> genV cx v
      Down _ v -> genV cx v
      Some v -> genV cx v
      Pack _ _ v -> genV cx v
      Inj i t UnitV | [l] <- either (const []) (:[]) (leafOf t) -> return ["((" ++ cType l ++ ")" ++ show i ++ ")"]
      Inj _ _ _ -> fail "a value sum with payloads"
      Tuple vs -> concat <$> mapM (genV cx) vs
      Ptr _ a -> (:[]) <$> genA cx 0 a
      Hole -> fail "a constructor context"
      Context _ _ -> fail "a constructor context"
      Null _ -> fail "the dummy value of a yield"

-- A boxed value, with the tag of the alternative that it is an injection into (0 outside a sum).
genA :: Ctx -> Int -> AVal -> G String
genA cx tag val
  = case val of
      Fun f -> genFun cx f
      UnitA -> return ("lean_box(" ++ show tag ++ ")")
      Roll _ v -> genA cx tag v
      InjA i _ v -> genA cx i v
      Box v -> genBox cx tag Nothing v
      BoxAt r v -> genBox cx tag (Just r) v
      Scalar v -> do VRaw r <- tyOf cx v
                     [e] <- genV cx v
                     return (boxScalar r e)
      Lam ps r e -> genLam cx ps r e
      InjLazy{} -> fail "a lazy value"
      OpenCon{} -> fail "an open constructor"

-- A constructor object: fresh, or in the block of a credit. The leaves are evaluated before
-- the block is written. All fields are written, so a block may come from any credit of its
-- size: its header gets the tag and the number of objects.
genBox :: Ctx -> Int -> Maybe Path -> VVal -> G String
genBox cx tag at v
  = do ls <- tyOf cx v >>= leavesOf
       pl <- liftQ (payload ls)
       es <- genV cx v
       tmps <- mapM (const (fresh "f")) es
       b <- fresh "b"
       alloc <- case at of
                  Nothing -> return (allocCtor tag pl)
                  Just r -> do rt <- tyOfName cx r
                               return $ case rt of
                                 V (VReuse Full _ _) -> call "lt_reuse_full" [localName r, show tag, show (plObjs pl)]
                                 _ -> call "lt_reuse" [localName r, allocCtor tag pl, show tag, show (plObjs pl)]
       return (stmtExpr ([cType l ++ " " ++ x ++ " = " ++ e ++ ";" | (l,x,e) <- zip3 ls tmps es]
                         ++ ["lean_object* " ++ b ++ " = " ++ alloc ++ ";"]
                         ++ [writeSlot pl b s x | (s,x) <- zip (plSlots pl) tmps]) b)

-- A top-level function as a closure. Lean's closures take objects, so its parameters and
-- result must be objects.
genFun :: Ctx -> Name -> G String
genFun cx f
  = case M.lookup f (envSigs (cxEnv cx)) of
      Just (SigFun _ ps _ r) ->
        do pls <- mapM (leavesOf . snd) ps
           rls <- leavesOf r
           tgt <- target cx f
           if all (== [LObj]) (rls : pls) && length ps <= closureMaxArgs
             then return (call "lean_alloc_closure" ["(void*)" ++ tgtName tgt, show (length ps), "0"])
             else fail ("the function " ++ show f ++ " as a closure")
      _ -> fail ("unknown function " ++ show f)

-- the largest number of arguments of a closure that `lean_apply_n` passes one by one
closureMaxArgs :: Int
closureMaxArgs = 16

-- A closure: a C function that takes the captured leaves (boxed, as Lean's closures hold
-- objects) and the parameters, which are objects, in an array if they are more than a closure
-- passes one by one. Applying it consumes the closure and passes the captures owned, as the
-- closure's body owns them.
genLam :: Ctx -> [(Path,Mode,VType)] -> VType -> VExpr -> G String
genLam cx ps r e
  = do let caps = S.toList (fvA (Lam ps r e))
       capLeaves <- forM caps $ \x -> do ls <- tyOfName cx x >>= leavesOfTy
                                         return (x,ls)
       pls <- mapM (\(_,_,t) -> leavesOf t) ps
       rls <- leavesOf r
       let fixed = [(l,n) | (x,ls) <- capLeaves, (l,n) <- zip ls (leafNames x (length ls))]
           arity = length fixed + length ps
       if not (all (== [LObj]) (rls : pls)) then fail "a closure with parameters or result that are not objects"
       else if LCredit `elem` map fst fixed then fail "a credit captured by a closure"
       else do
         fn <- fresh "lt_lam"
         cs <- mapM (const (fresh "c")) fixed
         body <- genE cx{ cxGamma = M.union (M.fromList [(x,V t) | (x,_,t) <- ps]) (cxGamma cx), cxJoins = M.empty } DReturn e
         let args = cs ++ [localName x | (x,_,_) <- ps]
             (params,loadArgs)
               | arity > closureMaxArgs = (["lean_object** _args"], [text ("lean_object* " ++ a ++ " = _args[" ++ show i ++ "];") | (i,a) <- zip [0 :: Int ..] args])
               | otherwise = (["lean_object* " ++ a | a <- args], [])
             loads = loadArgs ++ [text (cType l ++ " " ++ n ++ " = " ++ convert LObj l c ++ ";") | ((l,n),c) <- zip fixed cs]
         modify (\st -> st{ stLams = stLams st ++ ["static lean_object*" <+> text (call fn params) <+> block (loads ++ body)] })
         c <- fresh "clo"
         return (stmtExpr (("lean_object* " ++ c ++ " = " ++ call "lean_alloc_closure" ["(void*)" ++ fn, show arity, show (length fixed)] ++ ";")
                           : [call "lean_closure_set" [c, show i, convert l LObj n] ++ ";" | (i,(l,n)) <- zip [0 :: Int ..] fixed]) c)

------------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------------

-- where the result of an expression goes: returned, or assigned to the leaves of a binder
data Dest = DReturn | DAssign [String]

assignTo :: Dest -> [String] -> G [C]
assignTo dest es
  = case (dest,es) of
      (DReturn,[e]) -> return ["return" <+> text e <> ";"]
      (DReturn,[]) -> return ["return lean_box(0);"]
      (DAssign xs,_) | length xs == length es -> return [text (x ++ " = " ++ e ++ ";") | (x,e) <- zip xs es]
      _ -> fail "a result with several leaves"

-- the result of a call, which is a C expression even if the result has no leaves
assignCall :: Dest -> [Leaf] -> String -> G [C]
assignCall dest ls e
  = case ls of
      [] -> do s <- assignTo dest []
               return (text (e ++ ";") : s)
      _ -> assignTo dest [e]

genE :: Ctx -> Dest -> VExpr -> G [C]
genE cx dest expr
  = case expr of
      Ret v -> genV cx v >>= assignTo dest
      Let x t e1 e2 ->
        do ls <- leavesOf t
           s1 <- case e1 of
                   Ret v -> declare x ls <$> genV cx v
                   _ -> do s <- genE cx (DAssign (leafNames x (length ls))) e1
                           -- the binders of e1 are out of scope in e2
                           return (declareOnly x ls ++ [block s])
           s2 <- genE (bindVar cx x (V t)) dest e2
           return (s1 ++ s2)
      Unreachable _ -> return ["lean_internal_panic_unreachable();"]
      Dup x e ->
        do ls <- tyOfName cx x >>= leavesOfTy
           s <- genE cx dest e
           return ([text ("lean_inc(" ++ n ++ ");") | (LObj,n) <- zip ls (leafNames x (length ls))] ++ s)
      Drop x e ->
        do ls <- tyOfName cx x >>= leavesOfTy
           s <- genE cx dest e
           return (mapMaybe dropLeaf (zip ls (leafNames x (length ls))) ++ s)
      Free r e ->
        do rt <- tyOfName cx r
           s <- genE cx dest e
           let free = case rt of
                        V (VReuse Full _ _) -> text ("lean_free_object(" ++ localName r ++ ");")
                        _ -> text ("if (" ++ localName r ++ " != NULL) lean_free_object(" ++ localName r ++ ");")
           return (free : s)
      IsUnique x e1 e2 ->
        do t <- tyOfName cx x
           case t of
             A _ -> return ()
             V _ -> fail ("uniqueness test of an unboxed value: " ++ show x)
           s1 <- genE cx{ cxGamma = uniqueGamma (cxGamma cx) x } dest e1
           s2 <- genE cx dest e2
           return [ifElse ("lean_is_exclusive(" ++ localName x ++ ")") s1 s2]
      IfFull r e1 e2 ->
        do t <- tyOfName cx r
           full <- case t of
                     V (VReuse _ n p) -> return (V (VReuse Full n p))
                     _ -> fail ("test of a non-credit: " ++ show r)
           s1 <- genE (bindVar cx r full) dest e1
           s2 <- genE cx dest e2
           return [ifElse (localName r ++ " != NULL") s1 s2]
      UnboxRu z e ->
        do g <- liftQ (unboxRuGamma (cxGamma cx) z)
           s <- genE cx{ cxGamma = g } dest e
           return (text ("lean_object* " ++ localName (child z SCredit) ++ " = " ++ localName z ++ ";") : s)
      -- the credit needs no copy of the contents, as a box written into it writes all fields
      CopyRu z r e ->
        do g <- liftQ (copyRuGamma (cxGamma cx) z r)
           A a <- tyOfName cx z
           pl <- liftQ (boxContents a) >>= leavesOf >>= liftQ . payload
           s <- genE cx{ cxGamma = g } dest e
           return (text ("lean_object* " ++ localName r ++ " = " ++ allocCtor (boxTag z) pl ++ ";") : s)
      Gen _ e -> genE cx dest e
      CastEv _ _ e -> genE cx dest e
      Total k e -> genE (bindVar cx k (V VToken)) dest e
      Join j _ ps e1 e2 -> genJoins cx dest [(j,ps,e1)] False e2
      JoinRec _ ds e -> genJoins cx dest [(j,ps,e1) | JoinDef j _ ps e1 <- ds] True e
      Jump j _ vs ->
        do (lbl,xs,recursive) <- maybe (fail ("jump to unknown join point " ++ show j)) return (M.lookup j (cxJoins cx))
           targets <- concat <$> mapM (\(x,t) -> do ls <- leavesOf t
                                                    return (zip ls (leafNames x (length ls)))) xs
           args <- concat <$> mapM (genV cx) vs
           let goto = text ("goto " ++ lbl ++ ";")
           if recursive
             then do tmps <- mapM (const (fresh "a")) args
                     return [block ([text (cType l ++ " " ++ tmp ++ " = " ++ a ++ ";") | ((l,_),tmp,a) <- zip3 targets tmps args]
                                    ++ [text (n ++ " = " ++ tmp ++ ";") | ((_,n),tmp) <- zip targets tmps] ++ [goto])]
             else return ([text (n ++ " = " ++ a ++ ";") | ((_,n),a) <- zip targets args] ++ [goto])
      Call f _ vs -> genCall cx dest f vs
      App f vs ->
        do A (AFun _ r) <- tyOfName cx f
           args <- concat <$> mapM (genV cx) vs
           rls <- leavesOf r
           let n = length args
               app | n <= closureMaxArgs = return ([], call ("lean_apply_" ++ show n) (localName f : args))
                   | otherwise = do xs <- fresh "args"
                                    return (["lean_object* " ++ xs ++ "[] = {" ++ intercalate ", " args ++ "};"],
                                            call "lean_apply_m" [localName f, show n, xs])
           (pre,e) <- app
           s <- assignCall dest rls e
           return [block (map text pre ++ s)]
      Proj v i x e ->
        do t <- tyOf cx v
           (start,u) <- liftQ (fieldRange t i)
           ls <- leavesOf t
           us <- leavesOf u
           (pre,es) <- bindValue cx v ls
           body <- genE (bindVar cx x (V u)) dest e
           return (pre ++ declare x us (take (length us) (drop start es)) ++ body)
      Deref v x e ->
        do VPtr a <- tyOf cx v
           [ve] <- genV cx v
           body <- genE (bindVar cx x (A a)) dest e
           return (declare x [LObj] [ve] ++ body)
      Unroll v x e ->
        do A t <- tyOfName cx v
           a <- liftQ (dataBody (cxEnv cx) t)
           body <- genE (bindVar cx x (A a)) dest e
           return (declare x [LObj] [localName v] ++ body)
      -- the contents are read out of the block at once
      Unbox v x e ->
        do A a <- tyOfName cx v
           t <- liftQ (boxContents a)
           ls <- leavesOf t
           pl <- liftQ (payload ls)
           body <- genE (bindVar cx x (V t)) dest e
           return (declare x ls [readSlot pl (localName v) s | s <- plSlots pl] ++ body)
      Unscalar m v x e ->
        do A (AScalar r) <- tyOfName cx v
           body <- genE (bindVar cx x (V (VRaw r))) dest e
           let release = [text ("lean_dec(" ++ localName v ++ ");") | owning m]
           return (declare x [LScalar r] [unboxScalar r (localName v)] ++ release ++ body)
      CaseA v alts def ->
        do t <- tyOfName cx v
           tss <- liftQ (altTypes (cxEnv cx) t expr)
           brs <- forM (zip alts tss) $ \((i,x,e),ts) ->
                    do [ti] <- return ts
                       body <- genE (bindVar cx x ti) dest e
                       return (["case " ++ show i ++ ":"], declare x [LObj] [localName v] ++ body)
           fallback <- case (def, drop (length alts) tss) of
                         (Just (x,e), [[td]]) -> do body <- genE (bindVar cx x td) dest e
                                                    return [(["default:"], declare x [LObj] [localName v] ++ body)]
                         _ -> return []
           return (switch (tagRead t (localName v)) (brs ++ fallback))
      SplitA v k (x,e1) (y,e2) ->
        do t <- tyOfName cx v
           [[tl@(A lo)],[th@(A hi)]] <- liftQ (altTypes (cxEnv cx) t expr)
           let ve = localName v
               test = case (shapeIsHeap lo, shapeIsHeap hi) of
                        (Just False, Just True) -> "lean_is_scalar(" ++ ve ++ ")"
                        (Just True, Just False) -> "!lean_is_scalar(" ++ ve ++ ")"
                        _ -> tagRead t ve ++ " < " ++ show k
           s1 <- genE (bindVar cx x tl) dest e1
           s2 <- genE (bindVar cx y th) dest e2
           return [ifElse test (declare x [LObj] [ve] ++ s1) (declare y [LObj] [ve] ++ s2)]
      CaseV v alts ->
        do t <- tyOf cx v
           ls <- leavesOf t
           (pre,es) <- bindValue cx v ls
           ts <- case t of
                   VSum ts | [_] <- ls -> return ts
                   _ -> fail "a case on a value sum with payloads"
           brs <- forM alts $ \(i,x,e) ->
                    do body <- genE (bindVar cx x (V (snd (ts !! i)))) dest e
                       return (["case " ++ show i ++ ":"], body)
           return (pre ++ switch (head es) brs)
      IfWhnf{} -> fail "a lazy value"
      IfYielding{} -> fail "an effect yield"
      IsNull{} -> fail "a nullable value"
      Unpack{} -> fail "an existential"
      CaseLit{} -> fail "a case on literals"
      CaseOpen{} -> fail "an open datatype"
      Lock{} -> fail "a lazy value"
      Memoize{} -> fail "a lazy value"
      Append{} -> fail "a constructor context"
      Plug{} -> fail "a constructor context"
      CtxCopy{} -> fail "a constructor context"
  where
    dropLeaf (l,n) = case l of
                       LObj -> Just (text ("lean_dec(" ++ n ++ ");"))
                       LCredit -> Just (text ("if (" ++ n ++ " != NULL) lean_free_object(" ++ n ++ ");"))
                       LScalar _ -> Nothing

-- the leaves of a value, bound to locals first unless it is a variable (as they are read more
-- than once)
bindValue :: Ctx -> VVal -> [Leaf] -> G ([C],[String])
bindValue cx v ls
  = do es <- genV cx v
       case v of
         Var _ -> return ([],es)
         _ -> do xs <- mapM (const (fresh "v")) es
                 return ([text (cType l ++ " " ++ x ++ " = " ++ e ++ ";") | (l,x,e) <- zip3 ls xs es], xs)

-- the first leaf and the type of field i of a product
fieldRange :: VType -> Int -> Either String (Int,VType)
fieldRange (VProd fs) i
  | i < length fs = Right (sum (map (length . leaves . snd) (take i fs)), snd (fs !! i))
fieldRange _ _ = Left "projection of a non-product"

-- The tag of a boxed sum: in the header if every alternative is a block, the unboxed scalar if
-- none is, and otherwise either (`lean_obj_tag`).
tagRead :: Ty -> String -> String
tagRead t ve
  = case t of
      A a | shapeIsHeap a == Just True -> "lean_ptr_tag(" ++ ve ++ ")"
          | shapeIsHeap a == Just False -> "lean_unbox(" ++ ve ++ ")"
      _ -> "lean_obj_tag(" ++ ve ++ ")"

-- A switch over alternatives. Without a default, the last alternative is the default too.
switch :: String -> [([String],[C])] -> [C]
switch _ [(_,body)] = [block body]
switch tag brs
  = ["switch (" <> text tag <> ")" <+> block [hsep (map text (labels ++ ["default:" | lastAlt i, not hasDefault])) <+> block (body ++ ["break;"])
                                             | (i,(labels,body)) <- zip [0 :: Int ..] brs]]
  where
    hasDefault = any (("default:" `elem`) . fst) brs
    lastAlt i = i == length brs - 1

-- Join points: the parameters are declared before the scope, and each body follows it under
-- its label; the bodies of recursive join points only see their group.
genJoins :: Ctx -> Dest -> [(Name,[(Path,Mode,VType)],VExpr)] -> Bool -> VExpr -> G [C]
genJoins cx dest js recursive e
  = do lbls <- mapM (const (fresh "join")) js
       decls <- concat <$> sequence [do ls <- leavesOf t
                                        return (declareOnly x ls) | (_,ps,_) <- js, (x,_,t) <- ps]
       let points = M.fromList [(j,(lbl,[(x,t) | (x,_,t) <- ps],recursive)) | ((j,ps,_),lbl) <- zip js lbls]
           inner = if recursive then points else cxJoins cx
       s <- genE cx{ cxJoins = M.union points (cxJoins cx) } dest e
       bodies <- sequence [do s1 <- genE (foldl (\c (x,_,t) -> bindVar c x (V t)) cx{ cxJoins = inner } ps) dest e1
                              return [text lbl <> ":" <+> block s1] | ((_,ps,e1),lbl) <- zip js lbls]
       let end = head lbls ++ "_end"
           (skip,finish) = case dest of
                             DReturn -> ([],[])
                             DAssign _ -> ([text ("goto " ++ end ++ ";")], [text (end ++ ": ;")])
       return [block (decls ++ s ++ skip ++ intercalate skip bodies ++ finish)]

------------------------------------------------------------------------------
-- Calls
------------------------------------------------------------------------------

-- A call of a function of this module passes the leaves of the arguments; one of another
-- module converts them to its impure signature.
genCall :: Ctx -> Dest -> Name -> [VVal] -> G [C]
genCall cx dest f vs
  = do (ps,r) <- case M.lookup f (envSigs (cxEnv cx)) of
                   Just (SigFun _ ps _ r) -> return (map snd ps, r)
                   _ -> fail ("unknown function " ++ show f)
       rls <- leavesOf r
       tgt <- target cx f
       case (vs, r) of
         -- the conversion of a literal (`Decls.rawOfNat`) is a C literal
         ([Lit (LitInt n)], VRaw raw) | n >= 0, fmap leanName (rawOfNat raw) == Just f
           -> assignTo dest ["((" ++ cType (LScalar raw) ++ ")" ++ show n ++ "ULL)"]
         _ -> do args <- mapM (\v -> do es <- genV cx v
                                        ls <- tyOf cx v >>= leavesOf
                                        return (zip ls es)) vs
                 e <- callExpr tgt (zip ps args) rls
                 assignCall dest rls e

-- the C expression of a call, with its arguments (each with its parameter type and its leaves)
callExpr :: Target -> [(VType,[(Leaf,String)])] -> [Leaf] -> G String
callExpr tgt args rls
  = case tgtImpure tgt of
      Nothing -> finish (concatMap (map snd . snd) args) id
      Just (ips,ir) | length ips == length args ->
        do cargs <- concat <$> zipWithM impureArg ips (map snd args)
           r <- case (rls, impureLeaf ir) of
                  ([l], Just il) -> return (\e -> convert il l e)
                  _ -> return id
           finish cargs r
      Just _ -> fail ("the impure signature of " ++ tgtName tgt ++ " does not match its arguments")
  where
    finish cargs conv
      = case tgtCall tgt of
          Pattern -> return (conv (expand (tgtName tgt) cargs))
          _ -> return (conv (call (tgtName tgt) cargs))
    -- an argument at its impure parameter type: none for `lcVoid`, and none for an erased
    -- parameter of a C function of the runtime
    impureArg it as
      = case impureLeaf it of
          Nothing -> return []
          Just _ | Standard <- tgtCall tgt, isErased it -> return []
          Just il -> case as of
                       [(l,e)] -> return [convert l il e]
                       [] -> return ["lean_box(0)"]
                       _ -> fail ("an argument with several leaves for " ++ tgtName tgt)

-- an `@[extern]` pattern with its arguments for `#1`, `#2`, ...
expand :: String -> [String] -> String
expand pat args = go pat
  where
    go ('#':cs) | (ds@(_:_),rest) <- span (`elem` ['0'..'9']) cs, let i = read ds, i >= 1, i <= length args
      = args !! (i-1) ++ go rest
    go (c:cs) = c : go cs
    go [] = []

------------------------------------------------------------------------------
-- Definitions and the module
------------------------------------------------------------------------------

-- The prototype and definition of a definition, and its initialisation (for a value). A
-- definition has the C name of its declaration, even if calls go to its `@[extern]` entry.
genDef :: Env -> M.Map Name Target -> M.Map Name String -> Def -> G (C,C,[C])
genDef env tgts cnames def
  = case def of
      DefFun f _ args _ res body _ ->
        do name <- cname f
           params <- concat <$> mapM (\(x,_,t) -> do ls <- leavesOf t
                                                     return [cType l ++ " " ++ n | (l,n) <- zip ls (leafNames x (length ls))]) args
           rt <- leavesOf res >>= resultType
           let cx = cx0{ cxGamma = M.fromList [(x,V t) | (x,_,t) <- args] }
           ss <- genE cx DReturn body
           let sig = "LEAN_EXPORT" <+> text rt <+> text (call name params)
           return (sig <> ";", sig <+> block ss, [])
      DefVal x _ t body ->
        do name <- cname x
           ls <- leavesOf t
           rt <- resultType ls
           ss <- genE cx0 DReturn body
           let initf = "_init_" ++ name
           return ("LEAN_EXPORT" <+> text rt <+> text name <> ";",
                   "static" <+> text rt <+> text initf <> "(void)" <+> block ss,
                   [text (name ++ " = " ++ initf ++ "();")]
                   ++ [text ("if (!lean_is_scalar(" ++ name ++ ")) lean_mark_persistent(" ++ name ++ ");") | ls == [LObj]])
  where
    cx0 = Ctx env tgts M.empty M.empty
    cname f = maybe (fail ("no C name for " ++ show f)) return (M.lookup f cnames)

-- the prototypes of the functions and values of other modules that the module uses, and the
-- globals of the module's declarations with an `[init]` function (Lean's `emitFnDecls`)
prototypes :: D.Dump -> [C]
prototypes d
  = [ text p | c <- D.dumpConsts d, Just p <- [proto (linkTarget False (D.constLink c))] ]
    ++ [ text p | x <- D.dumpDecls d, D.Extern _ <- [D.declValue x]
                , Just p <- [if hasInitFn x then global (D.declLink x) else proto (linkTarget False (D.declLink x))] ]
  where
    global l = do (_,r) <- D.linkImpure l
                  return ("LEAN_EXPORT " ++ ctype r ++ " " ++ D.linkCName l ++ ";")
    proto tgt
      = case (tgtCall tgt, tgtImpure tgt) of
          (Pattern,_) -> Nothing
          (_,Nothing) -> Nothing
          (c,Just ([],r)) -> case c of
                               Direct -> Just ("extern " ++ ctype r ++ " " ++ tgtName tgt ++ ";")
                               _ -> Just (ctype r ++ " " ++ tgtName tgt ++ "();")
          (c,Just (ps,r)) ->
            let kept = [p | p <- ps, impureLeaf p /= Nothing, not (isStandard c && isErased p)]
            in Just (ctype r ++ " " ++ tgtName tgt ++ "(" ++ intercalate ", " (map ctype kept) ++ ");")
    ctype t = maybe "lean_object*" cType (impureLeaf t)

-- | The boxed version of a declaration (Lean's `mkBoxedVersion`), which Lean's closures and
-- other modules call instead of the declaration if its impure signature has a scalar, borrowed
-- or `lcVoid` parameter or a scalar result, if it is external, or if it has more parameters than
-- a closure passes one by one (`requiresBoxedVersion`). It takes every parameter as an object (in
-- an array beyond that), unboxes and releases the scalars, calls the declaration, releases the
-- borrowed objects and boxes a scalar result. Its C name is in the dump.
boxedFn :: D.Decl -> [C]
boxedFn x
  = case (D.linkImpure link, D.linkBoxed link) of
      (Just (ips,ir), Just boxedName) | needsBoxed ips ir
        -> let n = length ips
               xs = ["x_" ++ show i | i <- [1..n]]
               (params,loads)
                 | n > closureMaxArgs = (["lean_object** _args"], ["lean_object* " ++ x' ++ " = _args[" ++ show i ++ "];" | (i,x') <- zip [0 :: Int ..] xs])
                 | otherwise = (["lean_object* " ++ x' | x' <- xs], [])
               unboxes = concat [ [cType l ++ " " ++ x' ++ "_u = " ++ unboxScalar r x' ++ ";", "lean_dec(" ++ x' ++ ");"]
                                | (p,x') <- zip ips xs, Just l@(LScalar r) <- [impureLeaf (D.paramType p)] ]
               cargs = [ case l of { LScalar _ -> x' ++ "_u"; _ -> x' }
                       | (p,x') <- zip ips xs, Just l <- [impureLeaf (D.paramType p)]
                       , not (isStandard (tgtCall tgt) && isErased (D.paramType p)) ]
               app = case tgtCall tgt of
                       Pattern -> expand (tgtName tgt) cargs
                       _ -> call (tgtName tgt) cargs
               (rt,res) = case impureLeaf ir of
                            Just l@(LScalar r) -> (cType l, boxScalar r "res")
                            _ -> ("lean_object*", "res")
               releases = ["lean_dec(" ++ x' ++ ");" | (p,x') <- zip ips xs, D.paramBorrow p, impureLeaf (D.paramType p) == Just LObj]
           in ["LEAN_EXPORT lean_object*" <+> text (call boxedName params)
               <+> block (map text (loads ++ unboxes ++ [rt ++ " res = " ++ app ++ ";"] ++ releases ++ ["return " ++ res ++ ";"]))]
      _ -> []
  where
    link = D.declLink x
    tgt = linkTarget True link
    needsBoxed ips ir
      = (not (null ips) && (isScalar ir || any (\p -> isScalar (D.paramType p) || D.paramBorrow p || impureLeaf (D.paramType p) == Nothing) ips
                                || D.linkExtern link /= Nothing))
        || length ips > closureMaxArgs
    isScalar t = case impureLeaf t of { Just (LScalar _) -> True; _ -> False }

isStandard :: Call -> Bool
isStandard Standard = True
isStandard _ = False

-- The module's initializers, as Lean's `emitInitFn` and `emitLegacyInitFn` write them. The
-- runtime phase (or all phases) also initializes the module's values.
initFns :: [D.ModInit] -> [C] -> [C]
initFns inits valueInits = concatMap initFn inits
  where
    runtimeName = [D.initName i | i <- inits, D.initPhase i `elem` ["runtime","comptime"]]
    initFn i
      = [text ("lean_object* " ++ imp ++ "(uint8_t builtin);") | imp <- D.initImports i]
        ++ [text ("void " ++ D.initLean i ++ "();") | not (null (D.initLean i))]
        ++ [ text ("static bool " ++ flag ++ " = false;")
           , "LEAN_EXPORT lean_object*" <+> text (D.initName i) <> "(uint8_t builtin)" <+> block (
               [ "lean_object * res;"
               , text ("if (" ++ flag ++ ") return lean_io_result_mk_ok(lean_box(0));")
               , text (flag ++ " = true;") ]
               ++ [text (D.initLean i ++ "();") | not (null (D.initLean i))]
               ++ concat [ [text ("res = " ++ f ++ "(builtin);"), "if (lean_io_result_is_error(res)) return res;", "lean_dec_ref(res);"]
                         | f <- D.initImports i ++ (if D.initPhase i == "legacy" then runtimeName else []) ]
               ++ (if D.initPhase i `elem` ["runtime","all"] then valueInits else [])
               ++ ["return lean_io_result_mk_ok(lean_box(0));"]) ]
      where flag = "_G_" ++ D.initPhase i ++ "_initialized"

-- The initializers of an `[init]` declaration (an `initialize` or `builtin_initialize` with a
-- value, by the function that computes it) and of an `IO Unit` initializer, as Lean's
-- `emitDeclInit` writes them for the runtime phase, where builtin initializers take precedence.
-- The functions take only the world, which has no C parameter.
hasInitFn :: D.Decl -> Bool
hasInitFn x = not (null (initFnOf x))

initFnOf :: D.Decl -> [D.Name]
initFnOf x = [f | null (D.declParams x), f <- [f | D.BuiltinInitFn f <- D.declInit x] ++ [f | D.InitFn f <- D.declInit x]]

isUnitInit :: D.Decl -> Bool
isUnitInit x = any (`elem` [D.IOUnitInit, D.IOUnitBuiltinInit]) (D.declInit x)

declInitCode :: M.Map Name Target -> D.Decl -> Either String [C]
declInitCode tgts x
  | isUnitInit x = return (run (D.linkCName link) [])
  | f:_ <- initFnOf x
  = do tgt <- maybe (Left ("no C name for the initializer " ++ f)) Right (M.lookup (leanName f) tgts)
       let name = D.linkCName link
           value = "lean_io_result_get_value(res)"
       return $ run (tgtName tgt) $ case D.linkImpure link >>= impureLeaf . snd of
         Just (LScalar r) -> [name ++ " = " ++ unboxScalar r value ++ ";"]
         _ -> [name ++ " = " ++ value ++ ";", "if (!lean_is_scalar(" ++ name ++ ")) lean_mark_persistent(" ++ name ++ ");"]
  | otherwise = return []
  where
    link = D.declLink x
    run f after = map text (["res = " ++ f ++ "();", "if (lean_io_result_is_error(res)) return res;"] ++ after ++ ["lean_dec_ref(res);"])

-- The names with initializers (`inits`) in an order in which each comes after the declarations
-- whose values it reads, also through the functions that it calls, and otherwise in the order of
-- `roots` (the order of declaration, in which Lean initializes them). `uses` gives the names
-- that each declaration uses.
initOrder :: [Name] -> M.Map Name (S.Set Name) -> S.Set Name -> [Name]
initOrder roots uses inits = reverse (snd (foldl visit (S.empty,[]) roots))
  where
    visit (seen,acc) x
      | S.member x seen = (seen,acc)
      | otherwise = let (seen',acc') = foldl visit (S.insert x seen,acc) (S.toList (M.findWithDefault S.empty x uses))
                    in (seen', if S.member x inits then x : acc' else acc')

-- the top-level functions and values that an expression uses
namesE :: VExpr -> S.Set Name
namesE e = here <> getConst (descendE (const (Const S.empty)) (Const . namesV) (\_ e' -> Const (namesE e')) e)
  where here = case e of
                 Call f _ _ -> S.singleton f
                 _ -> S.empty

namesV :: VVal -> S.Set Name
namesV v = here <> getConst (descendV (Const . namesA) (Const . namesV) v)
  where here = case v of
                 Glob x _ -> S.singleton x
                 _ -> S.empty

namesA :: AVal -> S.Set Name
namesA a = case a of
             Fun f -> S.singleton f
             Lam _ _ e -> namesE e
             _ -> getConst (descendA (const (Const S.empty)) (Const . namesA) (Const . namesV) a)

-- the C `main` of a module with `main`, as Lean's `emitMainFn` writes it
mainFn :: D.Dump -> String -> D.Main -> [C]
mainFn d leanMain (D.Main n exitCode)
  = map text $
    [ "char ** lean_setup_args(int argc, char ** argv);"
    , "lean_object* run_main(int argc, char ** argv) {" ]
    ++ (if n == 2
          then [ "  lean_object* in = lean_box(0);"
               , "  int i = argc;"
               , "  while (i > 1) {"
               , "    lean_object* n;"
               , "    i--;"
               , "    n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);"
               , "    in = n;"
               , "  }"
               , "  return " ++ leanMain ++ "(in);" ]
          else [ "  return " ++ leanMain ++ "();" ])
    ++ [ "}"
       , "int main(int argc, char ** argv) {"
       , "  lean_object* res;"
       , "  argv = lean_setup_args(argc, argv);"
       , "  res = " ++ initMain ++ "(1 /* builtin */);"
       , "  lean_io_mark_end_initialization();"
       , "  if (lean_io_result_is_ok(res)) {"
       , "    lean_dec_ref(res);"
       , "    lean_init_task_manager();"
       , "    res = lean_run_main(&run_main, argc, argv);"
       , "  }"
       , "  lean_finalize_task_manager();"
       , "  if (lean_io_result_is_ok(res)) {"
       , "    int ret = " ++ (if exitCode then "lean_unbox_uint32(lean_io_result_get_value(res));" else "0;")
       , "    lean_dec_ref(res);"
       , "    return ret;"
       , "  } else {"
       , "    lean_io_result_show_error(res);"
       , "    lean_dec_ref(res);"
       , "    return 1;"
       , "  }"
       , "}" ]
  where
    initMain = head ([D.initName i | i <- D.dumpInits d, D.initPhase i == "runtime"]
                     ++ [D.initName i | i <- D.dumpInits d, D.initPhase i == "all"] ++ ["initialize"])

-- helpers for the generated code
prelude :: [C]
prelude
  = [ "static inline lean_object* lt_dup(lean_object* o) { lean_inc(o); return o; }"
    , "// the block of a full credit as a constructor object with a tag and a number of objects"
    , "static inline lean_object* lt_reuse_full(lean_object* r, unsigned tag, unsigned objs) {"
    , "  lean_ctor_set_tag(r, tag); r->m_other = objs; return r;"
    , "}"
    , "// the block of a credit that may be empty, or else a fresh constructor object"
    , "#define lt_reuse(r, fresh, tag, objs) ((r) == NULL ? (fresh) : lt_reuse_full(r, tag, objs))" ]

-- | The C file of a lowered program and the dump it was elaborated from, or the errors of the
-- definitions that could not be generated.
cgenModule :: D.Dump -> Program -> Either [String] String
cgenModule d prog
  = case runM (mapM genOne (progDefs prog)) () (St 0 []) of
      Left err -> Left [err]
      Right (rs,st)
        | errs@(_:_) <- [e | Left e <- rs] ++ [D.declName x ++ ": " ++ e | (x,Left e) <- declInits] -> Left errs
        | otherwise ->
            let ok = [x | Right x <- rs]
                inits = M.filter (not . null) $ M.fromListWith (flip (++)) $
                          [(defName def, i) | (def,Right (_,_,i)) <- zip (progDefs prog) rs]
                          ++ [(leanName (D.declName x), i) | (x,Right i) <- declInits]
                roots = map (leanName . D.declName) (D.dumpDecls d) ++ map defName (progDefs prog)
                uses = M.fromList ([(defName def, namesE (defBody def)) | def <- progDefs prog]
                                   ++ [(leanName (D.declName x), S.fromList (map leanName (initFnOf x))) | x <- D.dumpDecls d, hasInitFn x])
                leanMain = maybe "_lean_main" tgtName (M.lookup (leanName "main") tgts)
                doc = vsep ([ text ("// Lean compiler output (lidar-lean)")
                            , text ("// Module: " ++ D.dumpModule d)
                            , "#include <lean/lean.h>"
                            , "#if defined(__clang__)"
                            , "#pragma clang diagnostic ignored \"-Wunused-parameter\""
                            , "#pragma clang diagnostic ignored \"-Wunused-label\""
                            , "#pragma clang diagnostic ignored \"-Wunused-variable\""
                            , "#pragma clang diagnostic ignored \"-Wreturn-type\""
                            , "#pragma clang diagnostic ignored \"-Wsometimes-uninitialized\""
                            , "#elif defined(__GNUC__) && !defined(__CLANG__)"
                            , "#pragma GCC diagnostic ignored \"-Wunused-parameter\""
                            , "#pragma GCC diagnostic ignored \"-Wunused-label\""
                            , "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\""
                            , "#endif"
                            , "#ifdef __cplusplus"
                            , "extern \"C\" {"
                            , "#endif" ]
                            ++ prelude
                            ++ prototypes d
                            ++ [p | (p,_,_) <- ok]
                            ++ stLams st
                            ++ [c | (_,c,_) <- ok]
                            ++ concatMap boxedFn [x | x <- D.dumpDecls d, defined x]
                            ++ initFns (D.dumpInits d) (concat [inits M.! x | x <- initOrder roots uses (M.keysSet inits)])
                            ++ maybe [] (mainFn d leanMain) (D.dumpMain d)
                            ++ ["#ifdef __cplusplus", "}", "#endif"])
            in Right (renderString (layoutPretty (LayoutOptions Unbounded) doc) ++ "\n")
  where
    env = envOf prog
    tgts = targetsOf d
    declInits = [(x, declInitCode tgts x) | x <- D.dumpDecls d]
    cnames = M.fromList [(leanName (D.declName x), D.linkCName (D.declLink x)) | x <- D.dumpDecls d]
    -- the declarations that have a C function: the externs, and the functions that lowering kept
    funs = S.fromList [f | DefFun{ defName = f } <- progDefs prog]
    defined x = case D.declValue x of
                  D.Extern _ -> True
                  D.Body _ -> S.member (leanName (D.declName x)) funs
    -- a definition that fails leaves the state as it was
    genOne :: Def -> G (Either String (C,C,[C]))
    genOne def = do st <- get
                    case runM (genDef env tgts cnames def) () st of
                      Left err -> return (Left (show (defName def) ++ ": " ++ err))
                      Right (r,st') -> do put st'
                                          return (Right r)
