-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

{- C code generation from the typed IR (after Perceus).

  Unboxed types are represented as described in `Layout`. A boxed sum is a `kk_box_t`:
  the alternative with index `i` of a sum has kklib's tag `kkTag i`; unit alternatives are
  singletons and boxes are heap blocks. Externals are called with their Koka C types and their
  arguments are converted.

  The C code is a `Doc`: string literals are documents, and a list of documents is a list of statements.
-}
module Backend.Typed.CGen.CGen( CEnv(..), cgenModule, cgenMain ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( intercalate, sortOn )
import Data.Maybe( fromMaybe, isJust )
import qualified Numeric
import Control.Monad( forM, foldM, when )
import Lib.PPrint( Doc, text, string, int, integer, empty, isEmptyDoc, line, nest, align, vcat, hcat, hsep, punctuate, (<.>), (<+>), (<->) )
import qualified Common.Name as K
import Common.NamePrim( nameInt32, nameInternalInt32, nameInt64, nameSSizeT, nameInternalSSizeT, nameIntPtrT, nameByte )
import Lidar.Name
import Backend.Typed.LidarName( fromLidar )
import Platform.Runtime( showHFloat )
import Lidar.Syntax
import Lidar.Traversal( child, TestSide(..), boxTag, canonical, failingTo, fvA, fvE, fvV, holes, testSides, within )
import Lidar.Types( inst, isShape, isToken, unToken )
import Lidar.Env( Env(..), envOf, dataBody, openFields, boxContents, M, get, gets, liftE, modify, put, runM, state )
import Lidar.Query( Gamma, inferE, inferV, inferVar, noJoins, inferAVar, altTypes, unboxRuGamma, copyRuGamma, lockGamma, uniqueGamma )
import Lidar.Layout
import Lidar.Ground( Ground(..), GroundBind(..), groundValues, groundOrder )
import Backend.Typed.CGen.Layout hiding( dupExpr, dropStmt )
import Backend.Typed.CGen.Koka
import Backend.Typed.CGen.Decls( typeDecls, openPayload, openTagName )
import Backend.Typed.CGen.ReuseSlots( keptLeaves )

data CEnv = CEnv{ ceModName   :: Name
                , ceImports   :: [Name]       -- all imported modules (their headers, initialization and termination)
                }

-- generation monad

-- `stLocal`: whether the current definition uses declarations of the C file (static functions)
data St = St{ stUniq :: Int, stStructs :: M.Map String String, stOrder :: [String], stDecls :: [Doc], stWrappers :: S.Set Name
            , stLocal :: Bool }

-- `cxJoins`: the label and the parameters of each join point in scope, and whether it is
-- recursive (its jumps then assign the parameters in parallel)
data Ctx = Ctx{ cxEnv :: Env, cxCEnv :: CEnv, cxGamma :: Gamma
              , cxJoins :: M.Map Name (Doc,[(Path,VType)],Bool)
              , cxShared :: S.Set Path }   -- blocks known to be shared (the else branch of `IsUnique`, and its aliases)

type G a = M () St a

failG :: String -> G a
failG = fail

liftC :: Either String a -> G a
liftC = liftE

freshName :: String -> G String
freshName s = state (\st -> ("_" ++ s ++ show (stUniq st), st{ stUniq = stUniq st + 1 }))

fresh :: String -> G Doc
fresh s = text <$> freshName s

emitDecl :: Doc -> G ()
emitDecl d = modify (\st -> st{ stDecls = stDecls st ++ [d], stLocal = True })

-- names

localName :: Path -> Doc
localName (Path x ss) = text ("x_" ++ encode (show x) ++ concat ["_p_" ++ encode (stepName s) | s <- ss])
  where
    -- by index, as paths compare (a boxed alternative by kklib's tag)
    stepName s = case s of
                   SInjA i _ -> "inj" ++ show (kkTag i)
                   SInjV i _ -> "inj" ++ show i
                   SField i _ -> "field" ++ show i
                   _ -> show s

ktInitName :: Name -> String
ktInitName modName = cName modName ++ "__init"

ktDoneName :: Name -> String
ktDoneName modName = cName modName ++ "__done"

-- the path of a module's C files, without the extension (as Koka's)
modulePath :: Name -> FilePath
modulePath = K.moduleNameToPath . fromLidar

-- C syntax

cty :: CT -> Doc
cty ct = text (ctName ct)

-- a block with each statement on its own line
block :: [Doc] -> Doc
block ss = "{" <.> nest 2 (hcat [line <.> s | s <- ss, not (isEmptyDoc s)]) <-> "}"

-- a statement expression `({ s1; s2; e; })` with each statement on its own line
stmtExpr :: [Doc] -> Doc -> Doc
stmtExpr ss e = "({" <+> align (vcat (ss ++ [e <.> ";"])) <+> "})"

dupExpr :: CT -> Doc -> Doc
dupExpr ct e = maybe e (\f -> text f <.> "(" <.> e <.> ",_ctx)") (dupFun ct)

-- The constructor shape of a pointer, unfolding named types but not their
-- payloads. Opaque representations supply no such evidence. Guard alias
-- unfolding as well: a recursive name alone has no known representation.
pointerShape :: Env -> Ty -> Maybe AType
pointerShape env t
  = case t of
      V (VPtr a) -> shape S.empty a
      A a -> shape S.empty a
      _ -> Nothing
  where
    shape _ a | isShape a = Just a
    shape seen a = case a of
      ACon n _ | not (S.member n seen)
               , Just TypeDef{} <- M.lookup n (envTypes env)
               , Right b <- dataBody env a -> shape (S.insert n seen) b
      _ -> Nothing

-- The statement of `dup x`, if `x` needs one. Like aggregate dup helpers, keep field dups
-- inline: a call can spill another live field and enlarge even the unique path's stack frame.
-- Root dups may be tail calls, so leave their inlining to the C compiler.
dupStmt :: Ctx -> Path -> Ty -> CT -> Doc -> Doc
dupStmt cx x t CBox ve
  | Just a <- pointerShape (cxEnv cx) t
  = case shapeIsHeap a of
      Just False -> empty
      heap -> let f = case heap of
                        Just True -> "kk_datatype_ptr_dup"
                        _ -> "kk_datatype_dup"
              in if field
                   then (if heap == Just True then "kt_datatype_ptr_dup_inline" else "kt_datatype_dup_inline")
                          <.> "(" <.> ve <.> ",_ctx);"
                   else f <.> "(kk_datatype_unbox(" <.> ve <.> "),_ctx);"
  | field = "kt_box_dup_inline(" <.> ve <.> ",_ctx);"
  where field = case canonical x of { Path _ (_:_) -> True; _ -> False }
dupStmt _ _ _ ct ve = maybe empty (\f -> text f <.> "(" <.> ve <.> ",_ctx);") (dupFun ct)

dropStmt :: CT -> Doc -> Doc
dropStmt ct e = maybe empty (\f -> text f <.> "(" <.> e <.> ",_ctx);") (dropFun ct)

-- C types

ctype :: VType -> G CT
ctype t
  = do let ct = layout t
       mapM_ (uncurry defineStruct) (structDefs ct)
       return ct

defineStruct :: String -> String -> G ()
defineStruct name def
  = modify (\st -> if M.member name (stStructs st) then st
                   else st{ stStructs = M.insert name def (stStructs st), stOrder = stOrder st ++ [name] })

-- block types for boxes
blockType :: CT -> G Doc
blockType ct
  = do uncurry defineStruct (blockDef ct)
       return ("struct" <+> text (blockName ct))

-- types of values

tyOf :: Ctx -> VVal -> G VType
tyOf cx v = liftC (inferV (cxEnv cx) (cxGamma cx) v)

tyOfName :: Ctx -> Path -> G Ty
tyOfName cx x = liftC (inferVar (cxGamma cx) x)

ctOf :: Ty -> G CT
ctOf (V t) = ctype t
ctOf (A _) = return CBox

-- Translate a binary shape decision using the pointer bit when it identifies
-- the two sides; otherwise the decision uses their tag intervals.
pointerTest :: Doc -> AType -> AType -> Maybe Doc
pointerTest ve left right
  = case (shapeIsHeap left,shapeIsHeap right) of
      (Just l,Just r) | l /= r -> Just ((if l then empty else "!") <.> "kk_datatype_is_ptr(kk_datatype_unbox(" <.> ve <.> "))")
      _ -> Nothing

-- values

genV :: Ctx -> VVal -> G Doc
genV cx val
  = case val of
      Var x -> return (localName x)
      Glob x _ -> return (text (cName x))
      DupV v -> do t <- tyOf cx v
                   ct <- ctype t
                   e <- genV cx v
                   return (dupExpr ct e)
      UnitV -> return "kk_Unit"
      Lit lit -> genLit lit
      NoReuse _ _ -> return "kk_reuse_null"
      TyApp v _ -> genV cx v
      -- every pointer is a `kk_box_t`, `any*` included
      Up v -> genV cx v
      Down _ v -> genV cx v
      -- the representation of `V?` is that of `V`
      Some v -> genV cx v
      Null t -> ctype t >>= yieldedValue
      Ptr _ v -> genA cx v
      Pack _ _ v -> genV cx v
      Inj i t v
        | isEnum t -> do ct <- ctype t
                         return ("((" <.> cty ct <.> ")" <.> int i <.> ")")
        | otherwise
        -> do ct@(CSum alts) <- ctype t
              let scan = scanOf ct
              x <- fresh "v"
              e <- genV cx v
              let setAlt = case alts !! i of
                             Just _ -> x <.> "._cons.c" <.> int i <+> "=" <+> e <.> ";"
                             Nothing -> empty
              return (stmtExpr ([cty ct <+> x <.> ";", x <.> "._tag = kk_value_tag(" <.> int (i+1) <.> ");"]
                                ++ [x <.> "._cons._fields[" <.> int j <.> "] = kk_box_null();" | j <- [0..scan-2]]
                                ++ [setAlt]) x)
      Tuple _ -> do t <- tyOf cx val
                    genProd cx t (prodLeafVals val)
      Hole -> return "kk_box_null()"   -- the placeholder (`kk_cctx_hole`)
      Context b k -> genCtx cx b k

-- Contexts have the same two-box layout as Koka's `cctx`; convert at the boundary.
toCctx :: Doc -> Doc
toCctx e = "kt_pun(kk_std_core_types__cctx," <.> e <.> ")"

fromCctx :: CT -> Doc -> Doc
fromCctx ct e = "kt_pun(" <.> cty ct <.> "," <.> e <.> ")"

-- Construct a context with `kk_cctx_empty` or `kk_cctx_create`.
genCtx :: Ctx -> AType -> VVal -> G Doc
genCtx cx b k
  = do ct <- tyOf cx (Context b k) >>= ctype
       case k of
         Hole -> return (fromCctx ct "kk_cctx_empty(_ctx)")
         _ -> do (ss,res,hole) <- genHolePath (bindVar cx nameHole (V (VPtr b))) k
                 return (stmtExpr ss (fromCctx ct ("kk_cctx_create(" <.> res <.> "," <.> hole <.> ",_ctx)")))

-- An operation on contexts or cells is a C expression (`genOperation`), and so is `ctx-copy`
-- followed by plugging the copy (`copyPlug`).
isOperation :: VExpr -> Bool
isOperation expr
  = case expr of
      Append{} -> True
      Plug{} -> True
      CtxCopy{} -> True
      Memoize{} -> True
      _ -> isJust (copyPlug expr)

genOperation :: Ctx -> VExpr -> G Doc
genOperation cx expr
  = case expr of
      _ | Just (c,v) <- copyPlug expr -> genV cx v >>= plug "kk_cctx_apply" cx c
      Append c d -> genAppend cx c d
      Plug c v -> genV cx v >>= plug "kk_cctx_apply_linear" cx c
      CtxCopy c -> do ct <- tyOf cx c >>= ctype
                      ce <- genV cx c
                      x <- fresh "c"
                      return (stmtExpr [cty ct <+> x <+> "=" <+> ce <.> ";", "kt_ctx_copy(&" <.> x <.> ".f0,&" <.> x <.> ".f1,_ctx);"] x)
      Memoize c _ k v -> genBox cx k (In c) v
      _ -> failG ("not an operation: " ++ show expr)

-- `let c' = ctx-copy c in c'[v]`: plugging a copy of `c`
copyPlug :: VExpr -> Maybe (VVal,VVal)
copyPlug expr
  = case expr of
      Let x _ (CtxCopy c) (Plug (Var y) v) | y == x, S.notMember x (fvV v) -> Just (c,v)
      _ -> Nothing

-- Appending a nonempty context plugs its `res` into the hole and keeps its hole
-- (`kk_cctx_extend_linear`); `kk_cctx_compose_linear` handles a possibly empty second context.
genAppend :: Ctx -> VVal -> VVal -> G Doc
genAppend cx c d
  = do ct <- liftC (inferE (cxEnv cx) (cxGamma cx) noJoins (Append c d)) >>= ctype
       td <- tyOf cx d
       de <- genV cx d
       case td of
         VCtx Full _ _
           -> do y <- fresh "c"
                 ce <- genV cx c
                 return (stmtExpr ["kk_std_core_types__cctx" <+> y <+> "=" <+> toCctx de <.> ";"]
                           (fromCctx ct ("kk_cctx_extend_linear(" <.> toCctx ce <.> "," <.> y <.> ".res," <.> y <.> ".holeptr,_ctx)")))
         _ -> do ce <- genV cx c
                 return (fromCctx ct ("kk_cctx_compose_linear(" <.> toCctx ce <.> "," <.> toCctx de <.> ",_ctx)"))

-- fill the hole of a unique context in place (`kk_cctx_apply_linear`); a copy of a context
-- is filled in place if it is unique and copied with the child otherwise (`kk_cctx_apply`)
plug :: Doc -> Ctx -> VVal -> Doc -> G Doc
plug fill cx c ve
  = do ce <- genV cx c
       return (fill <.> "(" <.> toCctx ce <.> "," <.> ve <.> ",_ctx)")

-- Allocate a one-hole value (`genBox` records the context path in the header of each block on
-- the path to the hole): the statements, `res` and the address of the hole (`kk_field_addr_t`).
-- The address is bound before the context is used, as in `kk_cctx_extend_linear`.
genHolePath :: Ctx -> VVal -> G ([Doc],Doc,Doc)
genHolePath cx k
  = do r <- fresh "r"
       h <- fresh "h"
       ke <- genV cx k
       fields <- pathFields k
       bs <- mapM (const (fresh "b")) fields
       let parents = r : ["((" <.> bt <.> "*)" <.> x <.> ")->" <.> f | (x,(bt,f)) <- zip bs fields]
           steps = ["kk_block_t*" <+> x <+> "= kt_box_as_ptr(" <.> parent <.> ",_ctx);" | (x,parent) <- zip bs parents]
           (bt,f) = last fields
           hole = "kk_box_t" <+> h <+> "= kk_internal_ptr_box(&((" <.> bt <.> "*)" <.> last bs <.> ")->" <.> f <.> ",_ctx);"
       return (("kk_box_t" <+> r <+> "=" <+> ke <.> ";") : steps ++ [hole], r, h)
  where
    -- the type of each block on the path, and the member that leads to the hole
    pathFields v = case v of
                     Ptr _ a -> blockOf a
                     _ -> failG ("not a one-hole value: " ++ show v)
    blockOf a = case a of
                  Roll _ w -> blockOf w
                  InjA _ _ w -> blockOf w
                  InjLazy _ _ w -> blockOf w
                  Box v -> payload v
                  BoxAt _ v -> payload v
                  _ -> failG ("not a one-hole value: " ++ show a)
    payload v = do ct <- tyOf cx v >>= ctype
                   bt <- blockType ct
                   (member,inner) <- holeMember cx ct v
                   rest <- maybe (return []) pathFields inner
                   return ((bt,member) : rest)

-- the member of a payload that leads to the hole, and the nested one-hole value there
holeMember :: Ctx -> CT -> VVal -> G (Doc,Maybe VVal)
holeMember cx ct v
  = do (j,inner) <- leaf v 0
       let member = case ct of
                      CProd _ -> "p.f" <.> int j
                      _ -> "p"
       return (member,inner)
  where
    leaf v i = case v of
                 Hole -> return (i,Nothing)
                 Tuple ws -> do let (before,w:_) = break ((== 1) . holes) ws
                                tws <- mapM (tyOf cx) before
                                leaf w (i + sum (map (length . leaves) tws))
                 _ -> return (i,Just v)

-- Injections only contain construction forms, so their tag can be passed down to
-- the allocation; a box or unit outside a sum has index 0.
genA :: Ctx -> AVal -> G Doc
genA cx = genAIn cx 0

genAIn :: Ctx -> Int -> AVal -> G Doc
genAIn cx tag val
  = case val of
      Fun f -> staticFun f
      UnitA -> return ("kk_datatype_box(kk_datatype_from_tag((kk_tag_t)" <.> int (kkTag tag) <.> "))")
      Roll _ v -> genAIn cx tag v
      InjA i (ASum _) v -> genAIn cx i v
      InjA _ _ _ -> failG "injection into a non-sum"
      InjLazy _ _ v -> genAIn cx tag v
      Box v -> genBox cx tag Fresh v
      BoxAt r v -> genBox cx tag (At r) v
      Scalar v -> genScalar cx v
      OpenCon c tys vs -> genOpenCon cx c tys vs
      Lam ps r e -> genLam cx ps r e

prodLeafVals :: VVal -> [VVal]
prodLeafVals (Tuple vs) = concatMap prodLeafVals vs
prodLeafVals v = [v]

-- construct an unboxed product from values for its components
genProd :: Ctx -> VType -> [VVal] -> G Doc
genProd cx t vs
  = do parts <- forM vs $ \v -> do e <- genV cx v
                                   tv <- tyOf cx v
                                   return (e,tv)
       prodFrom t parts

-- an unboxed product from the C expressions of its components and their types
prodFrom :: VType -> [(Doc,VType)] -> G Doc
prodFrom t parts
  = do ct <- ctype t
       case ct of
         CProd _
           -> do -- each value covers some leaves
                 x <- fresh "p"
                 assigns <- assignLeaves x [(e, length (leaves s), s) | (e,s) <- parts] 0
                 return (stmtExpr ((cty ct <+> x <.> ";") : assigns) x)
         -- at most one value has a leaf
         _ -> case [e | (e,s) <- parts, not (null (leaves s))] of
                [e] -> return e
                _ -> return "kk_Unit"
  where
    assignLeaves _ [] _ = return []
    assignLeaves x ((e,n,s):rest) i
      = do as <- leafAssign x i n s e
           rs <- assignLeaves x rest (i+n)
           return (as ++ rs)
    leafAssign x i n s e
      | n == 0 = return ["(void)(" <.> e <.> ");"]
      | n == 1 = return [x <.> ".f" <.> int i <+> "=" <+> e <.> ";"]
      | otherwise = do sct <- ctype s
                       y <- fresh "q"
                       return ((cty sct <+> y <+> "=" <+> e <.> ";") :
                               [x <.> ".f" <.> int (i+j) <+> "=" <+> y <.> ".f" <.> int j <.> ";" | j <- [0..n-1]])

-- project a component (a range of leaves) from a product
projLeaves :: VType -> Doc -> Int -> VType -> G Doc
projLeaves whole e start part
  = do let n = length (leaves part)
       ct <- ctype part
       wct <- ctype whole
       case (n, wct) of
         _ | start == 0 && ct == wct -> return e
         (0,_) -> return "kk_Unit"
         (_,CProd _) | n == 1 -> return ("(" <.> e <.> ").f" <.> int start)
         (_,CProd _)
           -> do y <- fresh "q"
                 return (stmtExpr ((cty ct <+> y <.> ";") : [y <.> ".f" <.> int j <+> "= (" <.> e <.> ").f" <.> int (start+j) <.> ";" | j <- [0..n-1]]) y)
         _ -> return e

-- where the block of a box comes from
data Alloc = Fresh | At Path | In VVal

-- a box: freshly allocated, in the block of a
-- reuse credit, or over the block of a cell (whose old fields were taken, see `[lock]`, and
-- whose reference count is kept). A box on the path of a one-hole value records the context path with its header (see `genHolePath`).
genBox :: Ctx -> Int -> Alloc -> VVal -> G Doc
genBox cx tag at v
  = do t <- tyOf cx v
       ct <- ctype t
       e <- genV cx v
       bt <- blockType ct
       x <- fresh "b"
       cpath <- if holes v == 1
                  then do (member,_) <- holeMember cx ct v
                          return (Just ("(uint8_t)kk_field_index_of(" <.> bt <.> "," <.> member <.> ")"))
                  else return Nothing
       let scan = int (scanOf ct)
           path = fromMaybe "0" cpath
           box  = "kt_box_from_block(&" <.> x <.> "->_block,_ctx)"
           allocAt r = "kk_block_alloc_at_as(" <.> bt <.> "," <.> r <.> "," <.> scan <.> "," <.> path <.> ",(kk_tag_t)" <.> int (kkTag tag) <.> ",_ctx)"
           allocFresh = case cpath of
                          Nothing -> "kk_block_alloc_as(" <.> bt <.> "," <.> scan <.> ",(kk_tag_t)" <.> int (kkTag tag) <.> ",_ctx)"
                          Just _ -> allocAt "kk_reuse_null"
           setPath = maybe empty (\i -> x <.> "->_block.header._field_idx =" <+> i <.> ";") cpath
           store = do y <- fresh "p"
                      return ((cty ct <+> y <+> "=" <+> e <.> ";") : storeFrom ct x y)
       case at of
         Fresh -> do s <- store
                     return (stmtExpr ((bt <.> "*" <+> x <+> "=" <+> allocFresh <.> ";") : s) box)
         At r  -> do rt <- tyOfName cx r
                     let check = "_Static_assert(sizeof(" <.> bt <.> ") ==" <+> int (blockSize ct) <.> ",\"kt_reuse\");"
                     case rt of
                       V (VReuse Full _ _)
                         -> do y <- fresh "reuse_payload"
                               let field i = case ct of
                                               CProd _ -> ".f" <.> int i
                                               _ -> empty
                                   writes matches = [x <.> "->p" <.> field i <+> "=" <+> y <.> field i <.> ";"
                                                    | (i,same) <- zip [0..] matches, not same]
                                   setTag k | k == Just tag = empty
                                            | otherwise = x <.> "->_block.header.tag = (kk_tag_t)" <.> int (kkTag tag) <.> ";"
                                   setScan oldScan | oldScan == scanOf ct = empty
                                                   | otherwise = x <.> "->_block.header.scan_fsize =" <+> int (scanOf ct) <.> ";"
                                   -- A described credit is a unique block of its described payload,
                                   -- so its header only needs the new tag and scan size, where they differ,
                                   -- and only the fields that change are stored. Dups still run, in `y`.
                                   update = case keptLeaves rt t v of
                                              Just (k,oldScan,matches) -> [setTag k, setScan oldScan, setPath] ++ writes matches
                                              Nothing -> ("kk_block_init(&" <.> x <.> "->_block,sizeof(" <.> bt <.> ")," <.> scan <.> "," <.> path <.> ",(kk_tag_t)" <.> int (kkTag tag) <.> ");")
                                                         : storeFrom ct x y
                               return (stmtExpr ([check, cty ct <+> y <+> "=" <+> e <.> ";", bt <.> "*" <+> x <+> "= (" <.> bt <.> "*)" <.> localName r <.> ";"]
                                                 ++ update) box)
                       -- a credit that may be empty, which `ExpandReuse` did not test
                       _ -> do s <- store
                               return (stmtExpr ([check, bt <.> "*" <+> x <+> "=" <+> allocAt (localName r) <.> ";"] ++ s) box)
         In y  -> do v <- fresh "v"
                     ye <- genV cx y
                     let clear = "kt_block_clear(kt_box_as_ptr(" <.> ye <.> ",_ctx)," <.> scan <.> ",(kk_tag_t)" <.> int (kkTag tag) <.> ",_ctx)"
                     return (stmtExpr ([cty ct <+> v <+> "=" <+> e <.> ";", bt <.> "*" <+> x <+> "= (" <.> bt <.> "*)" <.> clear <.> ";",
                                        setPath] ++ storeFrom ct x v) box)

-- Store a payload `y` in the block `x`: a product field by field, as a whole struct copy can
-- also copy its padding, from a temporary on the stack.
storeFrom :: CT -> Doc -> Doc -> [Doc]
storeFrom ct x y
  = case ct of
      CUnit -> []
      CProd fs -> [x <.> "->p.f" <.> int i <+> "=" <+> y <.> ".f" <.> int i <.> ";" | (i,_) <- fs]
      _ -> [x <.> "->p =" <+> y <.> ";"]

-- A projection copies the field into a local.
genProjection :: Ctx -> Dest -> VVal -> Int -> Path -> VExpr -> G [Doc]
genProjection cx dest v j x e = do
  t <- tyOf cx v
  (start,u) <- liftC (fieldRange t j)
  (base,pre) <- case v of
    Var z -> return (localName z,[])
    _ -> do ve <- genV cx v
            z <- fresh "product"
            ct <- ctype t
            return (z,[cty ct <+> z <+> "=" <+> ve <.> ";"])
  p <- projLeaves t base start u
  ct <- ctype u
  body <- genE (bindVar cx x (V u)) dest e
  return (pre ++ [declare (cty ct) x p] ++ body)

-- the first leaf and the type of the field i of a product
fieldRange :: VType -> Int -> Either String (Int,VType)
fieldRange (VProd fs) i
  | i < length fs = Right (sum (map (length . leaves . snd) (take i fs)), snd (fs !! i))
fieldRange _ _ = Left "projection of a non-product"

-- `[deref]` and `[unroll]` keep the pointer
-- `x` is the same block as `y`, so it is shared if `y` is
shareAlias :: Ctx -> Path -> Path -> Ctx
shareAlias cx y x
  | S.member y (cxShared cx) = cx{ cxShared = S.insert x (cxShared cx) }
  | otherwise = cx

genAlias :: Ctx -> Dest -> Doc -> Path -> Ty -> VExpr -> G [Doc]
genAlias cx dest ve x t e
  = do s <- genE (bindVar cx x t) dest e
       return ([declare "kk_box_t" x ve] ++ s)

-- The contents of a box are loaded at once, while the box is alive.
genUnbox :: Ctx -> Dest -> Path -> Path -> VExpr -> G [Doc]
genUnbox cx dest v x e
  = do A a <- tyOfName cx v
       t <- liftC (boxContents a)
       ue <- unboxBlock t (localName v)
       genRead cx dest x t ue e

-- An owned read lets the runtime release a heap-backed scalar.
genUnscalar :: Ctx -> Dest -> Mode -> Path -> Path -> VExpr -> G [Doc]
genUnscalar cx dest m v x e
  = do A (AScalar r) <- tyOfName cx v
       genRead cx dest x (VRaw r) (unboxScalar m r (localName v)) e

-- bind the contents `ue : t` that were read from a box or scalar
genRead :: Ctx -> Dest -> Path -> VType -> Doc -> VExpr -> G [Doc]
genRead cx dest x t ue e
  = do ct <- ctype t
       s <- genE (bindVar cx x (V t)) dest e
       return ([declare (cty ct) x ue] ++ s)

-- `[unbox-ru]` of `z` takes its block as a credit, which may then be freed or written. Its
-- contents were already loaded at `[bunbox]`.
genUnboxRu :: Ctx -> Dest -> Path -> VExpr -> G [Doc]
genUnboxRu cx dest z e
  = do g' <- liftC (unboxRuGamma (cxGamma cx) z)
       s <- genE cx{ cxGamma = g' } dest e
       return (declare "kk_reuse_t" (child z SCredit) ("kt_box_as_ptr(" <.> localName z <.> ",_ctx)") : s)

-- `[copy-ru]` of `z` allocates a block with the header of `z` and copies its payload. The
-- header is not copied: the reference count of `z` may change concurrently if `z` is
-- thread-shared, and the copy needs a fresh one. The runtime's `kk_block_alloc_copy` would
-- dup the fields, which the copy does not own.
genCopyRu :: Ctx -> Dest -> Path -> Path -> VExpr -> G [Doc]
genCopyRu cx dest z r e
  = do g' <- liftC (copyRuGamma (cxGamma cx) z r)
       ct <- liftC (inferAVar (cxGamma cx) z >>= boxContents) >>= ctype
       bt <- blockType ct
       x <- fresh "copy"
       s <- genE cx{ cxGamma = g' } dest e
       let old = "((" <.> bt <.> "*)kt_box_as_ptr(" <.> localName z <.> ",_ctx))"
       return ([bt <.> "*" <+> x <+> "= kk_block_alloc_as(" <.> bt <.> "," <.> int (scanOf ct) <.> ",(kk_tag_t)" <.> int (kkTag (boxTag z)) <.> ",_ctx);",
                copyPayload ct x old,
                declare "kk_reuse_t" r ("&" <.> x <.> "->_block")] ++ s)
  where
    copyPayload CUnit _ _ = empty
    copyPayload _ x old = "memcpy(&" <.> x <.> "->p,&" <.> old <.> "->p,sizeof(" <.> x <.> "->p));"

-- `[lock]` of `z` takes its block as a cell, the pointer to the block, which is then written.
genLock :: Ctx -> Dest -> Path -> VExpr -> G [Doc]
genLock cx dest z e
  = do g' <- liftC (lockGamma (cxGamma cx) z)
       s <- genE cx{ cxGamma = g' } dest e
       return (declare "kk_box_t" (child z SCredit) (localName z) : s)

-- Koka's `box` of a scalar
genScalar :: Ctx -> VVal -> G Doc
genScalar cx v
  = do VRaw r <- tyOf cx v
       e <- genV cx v
       return (text (fst (primBox r)) <.> "(" <.> e <.> ",_ctx)")

unboxScalar :: Mode -> Raw -> Doc -> Doc
unboxScalar mode r e
  = let borrow = if owning mode then "KK_OWNED" else "KK_BORROWED"
    in text (snd (primBox r)) <.> "(" <.> e <.> "," <.> borrow <.> ",_ctx)"

-- Koka's box of a scalar is a heap block only on targets where the scalar is not immediate
-- (`scalarHeapSize`), and needs no drop elsewhere. Like kklib's unbox, which ignores
-- ownership there, this does not release a polymorphic `kk_box_any` either.
dropScalar :: Raw -> Doc -> Doc
dropScalar r e
  = let drop = dropStmt CBox e
    in case scalarHeapSize r of
         Nothing -> drop
         Just 0  -> empty
         Just n  -> "if (KK_INTF_SIZE <=" <+> int n <.> ")" <+> block [drop]

-- the payload of a box, which is never the dummy value of a yield (`[is-null]`)
unboxBlock :: VType -> Doc -> G Doc
unboxBlock t e
  = do ct <- ctype t
       case ct of
         CUnit -> return "kk_Unit"
         _ -> do bt <- blockType ct
                 return ("((" <.> bt <.> "*)kt_box_as_ptr(" <.> e <.> ",_ctx))->p")

-- The dummy value of a yield: Koka's `box-any` in every pointer, which the runtime may drop
-- (`kcompose`), as `kk_valuetype_unbox_from_any` makes it, with the null in its niche (`niche`).
yieldedValue :: CT -> G Doc
yieldedValue ct
  = return $ case (ct, niche ct) of
      (CUnit, _) -> "kk_Unit"
      (CBox, _) -> "kk_box_any(_ctx)"
      (CEnum _, _) -> enumNull ct
      (_, Just n@(_, leaf)) | leaf /= CBox
        -> stmtExpr [cty ct <+> "_kt_d = kt_yielded(" <.> cty ct <.> ");", nicheField n "_kt_d" <+> "=" <+> leafNull leaf <.> ";"] "_kt_d"
      _ -> "kt_yielded(" <.> cty ct <.> ")"

-- The null of a tag (of an enum or a value sum) is all ones, which is never a tag (`enumSize`,
-- and an odd word that is not one of the small integers 1..n); a pointer's is `box-any`.
leafNull :: CT -> Doc
leafNull leaf
  = case leaf of
      CSum _ -> "kt_null_tag"
      _ -> enumNull leaf

enumNull :: CT -> Doc
enumNull ct = "((" <.> cty ct <.> ")-1)"

-- the niche leaf of a value (`niche`): a pointer or a tag
nicheField :: ([Int],CT) -> Doc -> Doc
nicheField (path,leaf) e
  = let field = hcat (e : [".f" <.> int i | i <- path])
    in case leaf of
         CSum _ -> field <.> "._tag"
         _ -> field

-- whether the niche of a value is the null
nullTest :: ([Int],CT) -> Doc -> Doc
nullTest n@(_,leaf) e
  = let field = nicheField n e
    in case leaf of
         CBox -> "kt_is_box_any(" <.> field <.> ",_ctx)"
         CSum _ -> "kt_is_null_tag(" <.> field <.> ")"
         _ -> "(" <.> field <+> "==" <+> enumNull leaf <.> ")"

-- literals

genLit :: Lit -> G Doc
genLit lit
  = case lit of
      LitInt i -> return ("kt_box_integer(" <.> intLit i <.> ")")
      LitFloat d -> return (text (showHFloat d ""))
      LitChar c -> return ("((kk_char_t)" <.> int (fromEnum c) <.> ")")
      LitString "" -> return "kt_box_string(kk_string_empty())"
      LitString s -> do x <- fresh "s"
                        let (cstr,clen) = cstring s
                        return (stmtExpr ["kk_define_string_literal(static," <.> x <.> "," <.> int clen <.> "," <.> text cstr <.> ",_ctx);"]
                                         ("kt_box_string(kk_string_dup(" <.> x <.> ",_ctx))"))

-- Use a C literal when it fits; exclude the signed minimum, which is not a valid C literal.
intLit :: Integer -> Doc
intLit i
  | i >= -8191 && i <= 8191 = "kk_integer_from_small(" <.> integer i <.> ")"
  | abs i < 2^63 = "kk_integer_from_int64(KK_I64(" <.> integer i <.> "),_ctx)"
  | otherwise = "kk_integer_from_str(\"" <.> integer i <.> "\",_ctx)"

cstring :: String -> (String,Int)
cstring s
  = let (cs,ns) = unzip (map escape s) in ("\"" ++ concat cs ++ "\"", sum ns)
  where
    bytes bs = "\" \"" ++ concat ["\\x" ++ hex2 b | b <- bs] ++ "\" \""
    hex2 b = let h = Numeric.showHex b "" in if length h < 2 then '0':h else h
    escape c
      | c == '\0' = (bytes [0xC0,0x80], 2)
      | c < ' '   = (case c of { '\n' -> "\\n"; '\r' -> "\\r"; '\t' -> "\\t"; _ -> bytes [fromEnum c] }, 1)
      | c <= '\x7F' = (case c of { '"' -> "\\\""; '\'' -> "\\'"; '\\' -> "\\\\"; '?' -> "\\?"; _ -> [c] }, 1)
      | otherwise = let x = fromEnum c
                    in if x <= 0x7FF then (bytes [0xC0 + x `div` 64, 0x80 + x `mod` 64], 2)
                       else if x <= 0xFFFF then (bytes [0xE0 + x `div` 4096, 0x80 + (x `div` 64) `mod` 64, 0x80 + x `mod` 64], 3)
                       else (bytes [0xF0 + x `div` 262144, 0x80 + (x `div` 4096) `mod` 64, 0x80 + (x `div` 64) `mod` 64, 0x80 + x `mod` 64], 4)

-- top-level functions as values
staticFun :: Name -> G Doc
staticFun f
  = do modify (\st -> st{ stWrappers = S.insert f (stWrappers st), stLocal = True })
       x <- fresh "f"
       return (stmtExpr ["kk_define_static_function(" <.> x <.> "," <.> text (cName f) <.> "_fun,_ctx);"] ("kk_datatype_box(" <.> x <.> ")"))

-- closures
genLam :: Ctx -> [(Path,Mode,VType)] -> VType -> VExpr -> G Doc
genLam cx ps r e
  = do let caps = S.toList (lamFree ps e)
       capTys <- mapM (\x -> case M.lookup x (cxGamma cx) of
                               Just t -> return (x,t)
                               Nothing -> failG ("unbound captured variable " ++ show x)) caps
       capCts <- mapM (ctOf . snd) capTys
       -- the captures in memory order, like the fields of a product
       let fields = orderFields (zip [0..] capCts)
           scan   = 1 + sum (map (scanOf . snd) fields)
       n <- freshName "lam"
       let sname = "struct kt_clo" <.> text n
           fname = "kt_fun" <.> text n
       let (cps,tokens) = erased [(x,t) | (x,_,t) <- ps]
       pcts <- mapM (ctype . snd) cps
       rct  <- ctype r
       let structDef = sname <+> block ("struct kk_function_s _base;" : [cty ct <+> "c" <.> int i <.> ";" | (i,ct) <- fields]) <.> ";"
           g'  = M.union (M.fromList ([(x,V t) | (x,_,t) <- ps])) (cxGamma cx)
           cx' = cx{ cxGamma = g', cxJoins = M.empty }
       body <- genE cx' DReturn e
       -- Transfer captures from unique closures; shared closures retain their own references.
       let loads = [cty ct <+> localName (caps !! i) <+> "= _self->c" <.> int i <.> ";" | (i,ct) <- fields]
           dups = [x <+> "=" <+> dupExpr ct x <.> ";" | (i,ct) <- fields, needsRC ct, let x = localName (caps !! i)]
           sig = "static" <+> cty rct <+> fname <.> "(kk_function_t _fself" <.> hcat [", " <.> cty ct <+> localName x | ((x,_),ct) <- zip cps pcts] <.> ", kk_context_t* _ctx)"
           prologue | null caps = "kk_function_static_drop(_fself,_ctx);" : tokens
                    | otherwise = (sname <.> "* _self = kk_function_as(" <.> sname <.> "*,_fself,_ctx);") : loads
                                  ++ ["kk_drop_match(_self,{" <+> hsep dups <+> "},{},_ctx);"] ++ tokens
       emitDecl (vcat ([structDef | not (null caps)] ++ [sig <+> block (prologue ++ body)]))
       x <- fresh "c"
       let capVals = map localName caps
       -- A capture-free closure can share a static function block.
       if null caps
         then return (stmtExpr ["kk_define_static_function(" <.> x <.> "," <.> fname <.> ",_ctx);"]
                               ("kk_datatype_box(kk_function_static_dup(" <.> x <.> ",_ctx))"))
         else return (stmtExpr ([sname <.> "*" <+> x <+> "= kk_function_alloc_as(" <.> sname <.> "," <.> int scan <.> ",_ctx);",
                                 x <.> "->_base.fun = kk_kkfun_ptr_box(&" <.> fname <.> ",_ctx);"]
                                ++ [x <.> "->c" <.> int i <+> "=" <+> (capVals !! i) <.> ";" | (i,_) <- fields])
                               ("kt_box_from_block(&" <.> x <.> "->_base._block,_ctx)"))

lamFree :: [(Path,Mode,VType)] -> VExpr -> S.Set Path
lamFree ps e = fvA (Lam ps VUnit e)

-- The parameters of a function or closure in C: the effect token has no representation (see
-- "The effect token" in `Syntax`), so it is left out, and the body declares it as a local.
erased :: [(Path,VType)] -> ([(Path,VType)],[Doc])
erased ps = ([p | p@(_,t) <- ps, not (isToken t)], ["kk_unit_t" <+> localName x <+> "= kk_Unit;" | (x,t) <- ps, isToken t])

-- the arguments for the parameters of the types `ts` that C passes (`erased`)
passed :: [VType] -> [a] -> [a]
passed ts as = [a | (t,a) <- zip (ts ++ repeat VUnit) as, not (isToken t)]

-- An open constructor is a block of its tag string and its fields (`openPayload`), as Koka's.
genOpenCon :: Ctx -> Name -> [AType] -> [VVal] -> G Doc
genOpenCon cx c tys vs
  = do fields <- openConFields cx c tys
       let t = openPayload fields
       ct <- ctype t
       bt <- blockType ct
       args <- mapM (genV cx) vs
       payload <- prodFrom t (zip ("kk_box_dup(" <.> text (cName (openTagName c)) <.> ",_ctx)" : args) (map snd (prodFieldsOf t)))
       x <- fresh "b"
       y <- fresh "p"
       return (stmtExpr ([bt <.> "*" <+> x <+> "= kk_block_alloc_as(" <.> bt <.> "," <.> int (scanOf ct) <.> ",KK_TAG_OPEN,_ctx);",
                          cty ct <+> y <+> "=" <+> payload <.> ";"] ++ storeFrom ct x y)
                        ("kt_box_from_block(&" <.> x <.> "->_block,_ctx)"))
  where
    prodFieldsOf (VProd fs) = fs
    prodFieldsOf _ = []

-- the fields of an open constructor at type arguments
openConFields :: Ctx -> Name -> [AType] -> G [VType]
openConFields cx c tys
  = case M.lookup c (envSigs (cxEnv cx)) of
      Just (SigCon _ _ n) -> liftC (openFields (cxEnv cx) c (ACon n tys))
      _ -> failG ("unknown open constructor " ++ show c)

-- expressions

data Dest = DReturn | DAssign Doc | DDiscard

assignTo :: Dest -> CT -> Doc -> [Doc]
assignTo dest ct e
  = case dest of
      DReturn   -> ["return" <+> e <.> ";"]
      DAssign x -> [x <+> "=" <+> e <.> ";"]
      DDiscard  -> ["(void)(" <.> e <.> ");"]

bindVar :: Ctx -> Path -> Ty -> Ctx
bindVar cx x t = cx{ cxGamma = M.insert x t (cxGamma cx) }

-- Declare the C variable of a binder. A path is bound at most once in a scope (`Check`).
declare :: Doc -> Path -> Doc -> Doc
declare ctype x e = ctype <+> localName x <+> "=" <+> e <.> ";"

genE :: Ctx -> Dest -> VExpr -> G [Doc]
genE cx dest expr
  = case expr of
      Ret v -> do t <- tyOf cx v
                  ct <- ctype t
                  e <- genV cx v
                  return (assignTo dest ct e)
      _ | isOperation expr
        -> do ct <- liftC (inferE (cxEnv cx) (cxGamma cx) noJoins expr) >>= ctype
              e <- genOperation cx expr
              return (assignTo dest ct e)
      -- a copy that a bound plug fills is bound with the plug (`copyPlug`)
      Let x tx e1@CtxCopy{} (Let y t e2@(Plug (Var x') _) e3)
        | x' == x, S.notMember x (fvE e3) -> genE cx dest (Let y t (Let x tx e1 e2) e3)
      Let x t e1 e2
        -> do s1 <- genBound cx x t e1
              -- a shared cell stays shared once memoized
              let cx' = case e1 of
                          Memoize (Var c) _ _ _ -> shareAlias cx c x
                          _ -> cx
              s2 <- genE (bindVar cx' x (V t)) dest e2
              return (s1 ++ s2)
      -- the tokens are units (`erased`)
      IfYielding _ (k3,e3) (k2,e2)
        -> do s3 <- genE (bindVar cx k3 (V VToken)) dest e3
              s2 <- genE (bindVar cx k2 (V VToken)) dest e2
              let token k = "kk_unit_t" <+> localName k <+> "= kk_Unit;"
              return [ifChain [("kk_yielding(_ctx)",token k3 : s3)] (token k2 : s2)]
      Unreachable _ -> return ["kt_unreachable();"]
      Drop x e
        | S.member x (cxShared cx)   -- like Koka's C backend: a shared block only needs a decrement
        -> do t <- tyOfName cx x
              let ve = localName x
              s <- genE cx dest e
              let f = case pointerShape (cxEnv cx) t of
                        Just a | shapeIsSmall a -> "kk_block_decref_small"
                        _ -> "kk_block_decref"
              return ([f <.> "(kt_box_as_ptr(" <.> ve <.> ",_ctx),_ctx);"] ++ s)
        | otherwise
        -> do t <- tyOfName cx x
              let ve = localName x
              d <- case t of
                     A (AScalar r) -> return (dropScalar r ve)
                     _ -> (`dropStmt` ve) <$> ctOf t
              s <- genE cx dest e
              return (d : s)
      Free r e
        -> do rt <- tyOfName cx r
              s <- genE cx dest e
              let free = case rt of
                           V (VReuse Full _ _) -> "kt_reuse_free(" <.> localName r <.> ",_ctx);"
                           _ -> dropStmt CReuse (localName r)
              return (free : s)
      Dup x e
        -> do t <- tyOfName cx x
              ct <- ctOf t
              s <- genE cx dest e
              return (dupStmt cx x t ct (localName x) : s)
      IsUnique x e1 e2
        -> do t <- liftC (inferVar (cxGamma cx) x)
              s1 <- genE cx{ cxGamma = uniqueGamma (cxGamma cx) x } dest e1
              let xe = localName x
              let blockOf = "kt_box_as_ptr(" <.> xe <.> ",_ctx)"
              shared <- case t of
                          V (VCell _ _) -> return (S.insert x (cxShared cx))
                          V _ -> failG ("uniqueness test of an unboxed value: " ++ show x)
                          A _ -> return (S.insert x (cxShared cx))
              let test = "kk_block_is_unique(" <.> blockOf <.> ")"
              -- a unique cell is a credit, its block, under the same name in the first branch
              s1' <- case t of
                       V (VCell _ _) -> do b <- fresh "block"
                                           return ["kk_reuse_t" <+> b <+> "=" <+> blockOf <.> ";", block (declare "kk_reuse_t" x b : s1)]
                       _ -> return s1
              s2 <- genE cx{ cxShared = shared } dest e2
              return ["if kk_likely(" <.> test <.> ")" <+> block s1' <+> "else" <+> block s2]
      IfFull r e1 e2
        -> do t <- liftC (inferVar (cxGamma cx) r)
              full <- case t of
                        V (VReuse _ n p) -> return (V (VReuse Full n p))
                        _ -> failG ("test of a non-credit: " ++ show r)
              s1 <- genE (bindVar cx r full) dest e1
              s2 <- genE cx dest e2
              return ["if kk_likely(" <.> localName r <+> "!= kk_reuse_null)" <+> block s1 <+> "else" <+> block s2]
      UnboxRu v e -> genUnboxRu cx dest v e
      CopyRu z r e -> genCopyRu cx dest z r e
      Lock z e -> genLock cx dest z e
      Gen _ e -> genE cx dest e
      -- a no-op, as `?` and tokens have no representation of their own
      CastEv _ _ e -> genE cx dest e
      -- the token has no representation, so the result of e has the layout of the result
      Total k e -> genE (bindVar cx k (V VToken)) dest e
      Join j _ ps e1 e2 -> genJoins cx dest [(j,ps,e1)] False e2
      -- the bodies of recursive join points are a loop, which only sees the group itself
      JoinRec _ ds e -> genJoins cx dest [(j,ps,e1) | JoinDef j _ ps e1 <- ds] True e
      Jump j _ vs
        -> do (lbl,xs,recursive) <- maybe (failG ("jump to unknown join point " ++ show j)) return (M.lookup j (cxJoins cx))
              args <- mapM (genV cx) vs
              if recursive
                then do assigns <- parallelAssign xs args
                        return [block (assigns ++ ["goto" <+> lbl <.> ";"])]
                else return ([localName x <+> "=" <+> a <.> ";" | ((x,_),a) <- zip xs args] ++ ["goto" <+> lbl <.> ";"])
      Call f tys vs -> genCall cx dest f tys vs
      App f vs
        -> do ft <- tyOfName cx f
              (ps,r) <- case ft of
                          A (AFun ps r) -> return (map snd ps, r)
                          _ -> failG ("application of " ++ show ft)
              pcts <- mapM ctype (passed ps ps)
              rct  <- ctype r
              args <- mapM (genV cx) (passed ps vs)
              fx <- fresh "fn"
              let call = "kk_function_call(" <.> cty rct <.> ",(kk_function_t" <.> hcat [", " <.> cty ct | ct <- pcts] <.> ", kk_context_t*),"
                         <.> fx <.> ",(" <.> fx <.> hcat [", " <.> a | a <- args] <.> ", _ctx),_ctx)"
              return [block (("kk_function_t" <+> fx <+> "= kk_datatype_unbox(" <.> localName f <.> ");") : assignTo dest rct call)]
      Proj v i x e -> genProjection cx dest v i x e
      -- the value is bound before the test, which only a niche needs (`niche`): a full value, or
      -- one that admits null, takes the value branch
      IsNull v n (x,e)
        -> do VOrNull t <- tyOf cx v
              ct <- ctype t
              ve <- genV cx v
              s2 <- genE (bindVar cx x (V t)) dest e
              test <- case (t, niche ct) of
                        (VOrNull _, _) -> return Nothing
                        (_, nn) -> traverse (\nn' -> (,) (nullTest nn' (localName x)) <$> genE cx dest n) nn
              return (declare (cty ct) x ve : maybe s2 (\(c,s3) -> [ifChain [("kk_unlikely(" <.> c <.> ")",s3)] s2]) test)
      Unpack v tvs x e
        -> do VExists bs body <- tyOf cx v
              let t = inst bs (map AVar tvs) body
              ve <- genV cx v
              genRead cx dest x t ve e
      Deref v x e
        -> do VPtr a <- tyOf cx v
              ve <- genV cx v
              let cx' = case v of
                          Var y -> shareAlias cx y x
                          _ -> cx
              genAlias cx' dest ve x (A a) e
      Unroll v x e
        -> do A t <- tyOfName cx v
              a <- liftC (dataBody (cxEnv cx) t)
              genAlias (shareAlias cx v x) dest (localName v) x (A a) e
      Unbox v x e -> genUnbox cx dest v x e
      Unscalar m v x e -> genUnscalar cx dest m v x e
      _ | Just (tests,failure) <- conjunction expr
        -> genConjunction cx dest tests failure
      SplitA{} -> failG "a split is a conjunction"
      -- kklib's test needs the strict alternatives before the thunks, and only strict
      -- alternatives are immediate
      IfWhnf v (x,e1) (y,e2)
        -> do t <- tyOfName cx v
              [[ts@(A (ASum ss))],[tl@(A (ASum ls))]] <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
                  immediate = or [True | (_,AUnit) <- ss]
                  firstThunk = minimum (map fst ls)
                  test = (if immediate then "kk_datatype_is_whnf" else "kk_datatype_ptr_is_whnf")
                         <.> "(kk_datatype_unbox(" <.> ve <.> ")," <.> int (kkTag firstThunk) <.> ",_ctx)"
              when (maximum (map fst ss) > firstThunk)
                (failG ("the strict alternatives of a lazy sum must come before its thunks: " ++ show v))
              s1 <- genSumBranch cx dest v x ts e1
              s2 <- genSumBranch cx dest v y tl e2
              return [ifChain [("kk_likely(" <.> test <.> ")",s1)] s2]
      CaseA v alts def
        -> do t <- tyOfName cx v
              tss <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
              brs <- forM (zip alts tss) $ \((i,x,e),ts) -> do
                [ti] <- return ts
                body <- genSumBranch cx dest v x ti e
                return ([kkTag i],body)
              fallback <- case (def, drop (length alts) tss) of
                            (Just (x,e), [[td]]) -> Just <$> genSumBranch cx dest v x td e
                            _ -> return Nothing
              tg <- fresh "t"
              -- Match owns partitioning. A single alternative needs no test; two
              -- are a conjunction.
              case (brs,fallback) of
                ([(_,body)],Nothing) -> return [block body]
                _ -> return [block [tagDecl t tg ve, switchCases tg brs fallback]]
      -- a variable is a local, another value is copied into one
      CaseV v alts
        -> do t@(VSum ts) <- tyOf cx v
              ct <- ctype t
              ve <- genV cx v
              (decls,z) <- case v of
                             Var _ -> return ([],ve)
                             _ -> do w <- fresh "w"
                                     return ([cty ct <+> w <+> "=" <+> ve <.> ";"],w)
              brs <- forM alts $ \(i,x,e) ->
                       do let ti = snd (ts !! i)
                          cti <- ctype ti
                          let payload = case ct of
                                CSum alts' | Just _ <- alts' !! i -> z <.> "._cons.c" <.> int i
                                _ -> "kk_Unit"
                          body <- genE (bindVar cx x (V ti)) dest e
                          return ([i], declare (cty cti) x payload : body)
              let tag = case ct of { CEnum _ -> z; _ -> "kk_smallint_from_integer(" <.> z <.> "._tag) - 1" }
                  dispatch = case brs of
                    [(_,body)] -> body
                    [([i],first),(_,second)] -> [ifChain [("(" <.> tag <.> ") ==" <+> int i,first)] second]
                    _ -> [switchCases tag brs (Just ["kt_unreachable();"])]
              return [block (decls ++ dispatch)]
      CaseLit v alts def
        -> do tv <- tyOf cx v
              ve <- genV cx v
              brs <- forM alts $ \(l,e) ->
                       do s <- genE cx dest e
                          return (litTest ve l, s)
              sd <- genE cx dest def
              return [ifChain brs sd]
      Append{} -> failG "an operation"
      Plug{} -> failG "an operation"
      CtxCopy{} -> failG "an operation"
      Memoize{} -> failG "an operation"
      CaseOpen v alts def
        -> do let ve = localName v
              brs <- forM alts $ \(c,xs,e) ->
                       do tys <- openTypeArgs cx v
                          fields <- openConFields cx c tys
                          let t = openPayload fields
                          payload <- unboxBlock t ve
                          decls <- forM (zip3 xs fields (scanl (+) 1 (map (length . leaves) fields))) $ \(x,f,start) ->
                                     do fct <- ctype f
                                        e' <- projLeaves t payload start f
                                        return (declare (cty fct) x e')
                          s <- genE (foldl (\cx' (x,f) -> bindVar cx' x (V f)) cx (zip xs fields)) dest e
                          let tag = text (cName (openTagName c))
                          return ("kt_open_is(" <.> ve <.> ",kt_pun(kk_string_t," <.> tag <.> "),_ctx)", decls ++ s)
              sd <- genE cx dest def
              return [ifChain brs sd]

-- join points: the parameters are declared before the scope, and each body follows it under
-- its label; the bodies of recursive join points only see their group
genJoins :: Ctx -> Dest -> [(Name,[(Path,Mode,VType)],VExpr)] -> Bool -> VExpr -> G [Doc]
genJoins cx dest js recursive e
  = do lbls <- mapM (const (fresh "join")) js
       decls <- sequence [do ct <- ctype t
                             return (cty ct <+> localName x <.> ";") | (_,ps,_) <- js, (x,_,t) <- ps]
       let points = M.fromList [(j,(lbl,[(x,t) | (x,_,t) <- ps],recursive)) | ((j,ps,_),lbl) <- zip js lbls]
           inner = if recursive then points else cxJoins cx
       s <- genE cx{ cxJoins = M.union points (cxJoins cx) } dest e
       bodies <- sequence [do s1 <- genE (foldl (\c (x,_,t) -> bindVar c x (V t)) cx{ cxJoins = inner } ps) dest e1
                              return [lbl <.> ":" <+> block s1] | ((_,ps,e1),lbl) <- zip js lbls]
       let end = head lbls <.> "_end"
           (skip,finish) = case dest of
                             DReturn -> ([],[])
                             _ -> (["goto" <+> end <.> ";"], [end <.> ": ;"])
       return [block (decls ++ s ++ skip ++ intercalate skip bodies ++ finish)]

-- declare the binder of a `let` and assign it the value of the bound expression
genBound :: Ctx -> Path -> VType -> VExpr -> G [Doc]
genBound cx x t e
  = do ct <- ctype t
       s <- genE cx (DAssign (localName x)) e
       -- the binders of `e` are out of scope in the body, and a path may be bound in both
       let assign = case e of
                      Ret _ -> s
                      _ | isOperation e -> s
                      _ -> [block s]
       return ((cty ct <+> localName x <.> ";") : assign)

-- A partition binder is an alias with a different static sum and tag origin.
genSumBranch :: Ctx -> Dest -> Path -> Path -> Ty -> VExpr -> G [Doc]
genSumBranch cx dest v x t e
  = do body <- genE (bindVar cx x t) dest e
       return ([declare "kk_box_t" x (localName v)] ++ body)

-- Read the tag of a boxed sum; when every alternative is a heap block, the
-- tag is in the block header and needs no pointer test.
tagDecl :: Ty -> Doc -> Doc -> Doc
tagDecl t tg ve = "kk_tag_t" <+> tg <+> "=" <+> tagRead t ve <.> ";"

tagRead :: Ty -> Doc -> Doc
tagRead t ve = (case t of
                  A a | shapeIsHeap a == Just True -> "kt_heap_tag"
                  _ -> "kt_tag") <.> "(" <.> ve <.> ",_ctx)"

-- Consecutive tests with one failure (`failingTo`) form one condition, like a pattern
-- level in Koka's C backend, so that the C compiler evaluates them together: with
-- separate branches it sinks the loads of later operands behind earlier tests. The
-- operands are in scope before the first test. A single test is a conjunction of one;
-- the failure keeps the binder of its first test.
conjunction :: VExpr -> Maybe ([TestSide],(Path,VExpr))
conjunction expr
  = case sortOn (negate . length . fst) [(s : more (snd (sideOther s)) [fst (sideTaken s)] (snd (sideTaken s)),sideOther s) | s <- testSides expr, combinable s] of
      (c:_) -> Just c
      [] -> Nothing
  where
    more failure xs e
      = case failingTo failure e of
          Just s | combinable s, not (any (\u -> any (u `within`) xs) (fvE (sideRebuild s unused unused)))
            -> s : more failure (fst (sideTaken s) : xs) (snd (sideTaken s))
          _ -> []
    unused = Unreachable VUnit
    -- the payload of a sum value is read twice
    combinable s = case sideTest s of
                     CaseV v _ -> case v of { Var _ -> True; _ -> False }
                     _ -> True

genConjunction :: Ctx -> Dest -> [TestSide] -> (Path,VExpr) -> G [Doc]
genConjunction cx dest sides (_,failure)
  = do tests <- mapM (twoWay cx . sideTest) sides
       let taken = [if sideFirst s then (c,a) else ("!(" <.> c <.> ")",b) | (s,(c,a,b)) <- zip sides tests]
           other = case (sides,tests) of
                     (s:_,(_,a,b):_) -> if sideFirst s then b else a
                     _ -> error "Backend.Typed.CGen.genConjunction: no test"
           bind c (x,t,_) = bindVar c x t
           decl (_,_,d) = d
           cond = case taken of
                    [(c,_)] -> c
                    _ -> hcat (punctuate " && " ["(" <.> c <.> ")" | (c,_) <- taken])
       yes <- genE (foldl bind cx (map snd taken)) dest (snd (sideTaken (last sides)))
       no <- genE (bind cx other) dest failure
       return [ifChain [(cond,map (decl . snd) taken ++ yes)] (decl other : no)]

-- The condition of the first alternative of a test with two alternatives, and the binder
-- of each alternative with its type and declaration.
twoWay :: Ctx -> VExpr -> G (Doc,(Path,Ty,Doc),(Path,Ty,Doc))
twoWay cx expr
  = case expr of
      SplitA v k (x,_) (y,_)
        -> do t <- tyOfName cx v
              [[tl@(A ls)],[tr@(A rs)]] <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
              return (fromMaybe (tagRead t ve <+> "<" <+> int (kkTag k)) (pointerTest ve ls rs), alias v x tl, alias v y tr)
      CaseA v [(i,x,_)] (Just (y,_)) -> tagged v i x y
      CaseA v [(i,x,_),(_,y,_)] Nothing -> tagged v i x y
      CaseV v@(Var _) [(i,x,_),(j,y,_)]
        -> do t@(VSum ts) <- tyOf cx v
              ct <- ctype t
              z <- genV cx v
              let tag = case ct of { CEnum _ -> z; _ -> "kk_smallint_from_integer(" <.> z <.> "._tag) - 1" }
                  payload k = case ct of
                    CSum alts | Just _ <- alts !! k -> z <.> "._cons.c" <.> int k
                    _ -> "kk_Unit"
                  binder k w = do let tk = snd (ts !! k)
                                  ctk <- ctype tk
                                  return (w,V tk,declare (cty ctk) w (payload k))
              a <- binder i x
              b <- binder j y
              return ("(" <.> tag <.> ") ==" <+> int i,a,b)
      _ -> failG "twoWay: not a test with two alternatives"
  where
    alias v x t = (x,t,declare "kk_box_t" x (localName v))
    tagged v i x y = do t <- tyOfName cx v
                        [[ti],[to]] <- liftC (altTypes (cxEnv cx) t expr)
                        return (tagRead t (localName v) <+> "==" <+> int (kkTag i),alias v x ti,alias v y to)

-- The final arm of an exhaustive boxed case is the default, so that the switch
-- needs no unreachable case (without emitting its body twice).
switchCases :: Doc -> [([Int],[Doc])] -> Maybe [Doc] -> Doc
switchCases tag brs def
  = "switch (" <.> tag <.> ")" <+> block ([branch (["case" <+> int t <.> ":" | t <- tags]
                                                    ++ ["default:" | Nothing <- [def], i == length brs - 1]) body
                                           | (i,(tags,body)) <- zip [0..] brs]
                                          ++ [branch ["default:"] body | Just body <- [def]])
  where
    branch labels body = hsep labels <+> block (body ++ ["break;"])

-- the tests in order, each with its branch, and the final `else` branch
ifChain :: [(Doc,[Doc])] -> [Doc] -> Doc
ifChain [] other = block other
ifChain ((test,s):rest) other = "if (" <.> test <.> ")" <+> block s <+> "else" <+> ifChain rest other

litTest :: Doc -> Lit -> Doc
litTest ve lit
  = case lit of
      LitInt i -> "kk_integer_eq_borrow(kt_unbox_integer(" <.> ve <.> ")," <.> intLit i <.> ",_ctx)"
      LitString s -> "(kk_string_cmp_cstr_borrow(kt_unbox_string(" <.> ve <.> ")," <.> text (fst (cstring s)) <.> ",_ctx) == 0)"
      LitChar c -> "(" <.> ve <+> "==" <+> int (fromEnum c) <.> ")"
      LitFloat d -> "(" <.> ve <+> "==" <+> text (showHFloat d "") <.> ")"

openTypeArgs :: Ctx -> Path -> G [AType]
openTypeArgs cx v
  = do t <- tyOfName cx v
       case t of
         A (ACon _ args) -> return args
         _ -> return []

-- calls

genCall :: Ctx -> Dest -> Name -> [AType] -> [VVal] -> G [Doc]
genCall cx dest f tys vs
  | [Lit (LitInt i)] <- vs, Just (kt,lit) <- fixedWidthLit f i
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       return (assignTo dest rct (fromKoka kt rct lit))
  | Just ext <- M.lookup f (envExterns (cxEnv cx)) = genExtern cx dest f tys vs ext
  | otherwise
  = do (ps,r) <- callSig cx f tys
       rct <- ctype r
       args <- mapM (genV cx) (passed ps vs)
       return (assignTo dest rct (text (cName f) <.> "(" <.> hcat [a <.> ", " | a <- args] <.> "_ctx)"))

-- assign the arguments to the parameters through temporaries, as they may read the parameters
parallelAssign :: [(Path,VType)] -> [Doc] -> G [Doc]
parallelAssign params args
  = do tmps <- mapM (const (fresh "a")) args
       pcts <- mapM (ctype . snd) params
       return ([cty ct <+> t <+> "=" <+> a <.> ";" | (t,a,ct) <- zip3 tmps args pcts]
               ++ [localName p <+> "=" <+> t <.> ";" | ((p,_),t) <- zip params tmps])

-- Conversions of small integer literals to fixed-width integers become C literals
-- (as in `Backend.C.FromCore.genAppSpecial`); `ssize_t` and `intptr_t` stay within 32 bits
-- so that they fit on every platform.
fixedWidthLit :: Name -> Integer -> Maybe (String,Doc)
fixedWidthLit name i
  | f `elem` [nameInt32,nameInternalInt32] && within 31 = Just ("int32_t", "KK_I32(" <.> integer i <.> ")")
  | f == nameInt64 && within 63                         = Just ("int64_t", "KK_I64(" <.> integer i <.> ")")
  | f `elem` [nameSSizeT,nameInternalSSizeT] && within 31 = Just ("kk_ssize_t", "KK_IZ(" <.> integer i <.> ")")
  | f == nameIntPtrT && within 31                       = Just ("intptr_t", "KK_IP(" <.> integer i <.> ")")
  | f == nameByte && i >= 0 && i <= 255                 = Just ("uint8_t", "((uint8_t)" <.> integer i <.> ")")
  | otherwise = Nothing
  where
    f = fromLidar name
    within bits = abs i < 2^bits   -- excludes the minimum, which is not a valid C literal

callSig :: Ctx -> Name -> [AType] -> G ([VType],VType)
callSig cx f tys
  = case M.lookup f (envSigs (cxEnv cx)) of
      Just (SigFun tvs ps _ r) -> return (map (inst tvs tys . snd) ps, inst tvs tys r)
      _ -> failG ("unknown function " ++ show f)

genExtern :: Ctx -> Dest -> Name -> [AType] -> [VVal] -> Extern -> G [Doc]
genExtern cx dest f tys vs ext
  = do (ps0,r0) <- callSig cx f tys
       -- the token has no representation, so a result `W ⊗ KCtx` is a `W` in C
       let ps = passed ps0 ps0
           r = fromMaybe r0 (unToken r0)
       rct <- ctype r
       args <- forM (zip3 (passed ps0 vs) ps (map snd (extParams ext) ++ repeat KBox)) $ \(v,p,kp) ->
                 do e <- genV cx v
                    ct <- ctype p
                    return (toKoka ct (externCType f kp p) e, externCType f kp p)
       let fmt   = extFormat ext
           named = [(n,a) | (n,a) <- zip (map (show . fst) (extParams ext)) args, n `elem` cIdents fmt]
           call | isComment fmt = empty
                | null named    = substFormat fmt (map fst args)
                | otherwise     = stmtExpr [text kt <+> text n <+> "=" <+> a <.> ";" | (n,(a,kt)) <- named]  -- parameters used by name
                                           (substFormat fmt (map fst args))
       case r of
         VUnit | isEmptyDoc call -> return (assignTo dest CUnit "kk_Unit")
         VUnit -> return (("(void)(" <.> call <.> ");") : assignTo dest CUnit "kk_Unit")
         _ -> return (assignTo dest rct (fromKoka (externCType f (extResult ext) r) rct call))

-- definitions

genDef :: Env -> CEnv -> Def -> G (Doc,Doc,Doc)
genDef env cenv def
  = case def of
      DefFun f _ args _ res body _
        -> do let (cps,tokens) = erased [(x,t) | (x,_,t) <- args]
              pcts <- mapM (ctype . snd) cps
              rct  <- ctype res
              let g  = M.fromList [(x,V t) | (x,_,t) <- args]
                  cx = Ctx env cenv g M.empty S.empty
              ss <- genE cx DReturn body
              let sig = cty rct <+> text (cName f) <.> "(" <.> hcat [cty ct <+> localName x <.> ", " | ((x,_),ct) <- zip cps pcts] <.> "kk_context_t* _ctx)"
              return (sig <.> ";", sig <+> block (tokens ++ ss), empty)
      DefVal x _ t body
        -> do ct <- ctype t
              let cx = Ctx env cenv M.empty M.empty S.empty
              ss <- genE cx DReturn body
              let name  = text (cName x)
                  initf = name <.> "_init"
              return ("extern" <+> cty ct <+> name <.> ";",
                      vcat [cty ct <+> name <.> ";", "static" <+> cty ct <+> initf <.> "(kk_context_t* _ctx)" <+> block ss],
                      name <+> "=" <+> initf <.> "(_ctx);")

-- wrappers for top-level functions used as values
genWrapper :: Env -> CEnv -> Name -> G (Doc,Doc)
genWrapper env cenv f
  = case M.lookup f (envSigs env) of
      Just (SigFun tvs ps _ r)
        -> do let xs  = [root (newHiddenName ("p" ++ show i)) | i <- [0..length ps - 1]]
                  (cps,tokens) = erased [(x,t) | (x,(_,t)) <- zip xs ps]
              pcts <- mapM (ctype . snd) cps
              rct  <- ctype r
              let cx  = Ctx env cenv (M.fromList [(x,V t) | (x,(_,t)) <- zip xs ps]) M.empty S.empty
              body <- genCall cx DReturn f (map AVar tvs) (map Var xs)
              let sig = "static" <+> cty rct <+> text (cName f) <.> "_fun(kk_function_t _fself" <.> hcat [", " <.> cty ct <+> localName x | ((x,_),ct) <- zip cps pcts] <.> ", kk_context_t* _ctx)"
              return (sig <.> ";", sig <+> block (("kk_function_static_drop(_fself,_ctx);" : tokens) ++ body))
      _ -> failG ("wrapper for unknown function " ++ show f)

-- static ground values

{- A ground value (`Lidar.Ground`) is static data: blocks with a stuck reference count
  (`KK_HEADER_STATIC`), which kklib never counts or frees, and strings that are valid UTF-8 as
  normal bytes blocks.
  A block pointer is its address (the typed C assumes uncompressed pointers, as its layouts do).
  Top-level functions as values stay initialised, as their static blocks are filled on first
  use (`kk_define_static_function`).
-}

-- what the leaves of a ground value are made of: its locals and the ground globals written so
-- far (as C constants, one per leaf), the types of its locals, and the prefix of its block names
data SCtx = SCtx{ scEnv :: Env, scLocals :: M.Map Path [Doc], scGamma :: Gamma, scGlobals :: M.Map Name [Doc], scBase :: String }

-- The initialisers of the ground values of a program that can be written statically; their
-- blocks go to the declarations of the C file. A value that cannot be written, or that refers
-- to one that cannot, is initialised as before.
staticValues :: Program -> G (M.Map Name Doc)
staticValues prog
  = do (inits,_,blocks) <- foldM one (M.empty,M.empty,[]) (groundOrder grounds)
       when (not (null blocks)) (emitDecl (vcat (reverse blocks)))
       return inits
  where
    env = envOf prog
    grounds = groundValues (const False) prog
    types = M.fromList [(x,t) | DefVal x _ t _ <- progDefs prog]
    one :: (M.Map Name Doc,M.Map Name [Doc],[Doc]) -> Name -> G (M.Map Name Doc,M.Map Name [Doc],[Doc])
    one acc@(inits,globals,blocks) x
      = do st <- get
           case runM (staticValue (SCtx env M.empty M.empty globals (cName x)) (types M.! x) (grounds M.! x) blocks) () st of
             Right ((ini,ls,blocks'),st') -> do put st'
                                                return (M.insert x ini inits, M.insert x ls globals, blocks')
             Left _ -> return acc

-- the initialiser and the leaves of a ground value of type t, and the blocks written so far
-- (last first) with its own
staticValue :: SCtx -> VType -> Ground -> [Doc] -> G (Doc,[Doc],[Doc])
staticValue sc0 t (Ground binds res) blocks0
  = do (sc,blocks) <- foldM bind (sc0,blocks0) binds
       (ls,blocks') <- staticLeaves sc blocks res
       ct <- ctype t
       ini <- staticInit ct ls
       return (ini,ls,blocks')
  where
    bind (sc,blocks) (x,tx,b)
      = case b of
          GValue v -> do (ls,blocks') <- staticLeaves sc blocks v
                         return (sc{ scLocals = M.insert x ls (scLocals sc), scGamma = M.insert x (V tx) (scGamma sc) }, blocks')
          GCall f _ _ -> failG ("cannot fold " ++ show f)

-- the C constants of the leaves of a ground value, and the blocks written so far with its own
staticLeaves :: SCtx -> [Doc] -> VVal -> G ([Doc],[Doc])
staticLeaves sc blocks val
  = case val of
      Var x -> found (M.lookup x (scLocals sc))
      Glob g _ -> found (M.lookup g (scGlobals sc))
      DupV v -> staticLeaves sc blocks v
      UnitV -> return ([],blocks)
      Lit (LitInt i) -> return (["((kk_intb_t)" <.> integer (4*i + 1) <.> ")"],blocks)   -- `kk_integer_from_small`
      Lit (LitChar c) -> return (["((kk_char_t)" <.> int (fromEnum c) <.> ")"],blocks)
      Lit (LitString "") -> return (["kk_datatype_tag_init(1)"],blocks)                   -- `kk_string_empty`
      -- as `kk_string_alloc_from_utf8n` leaves it, which converts invalid UTF-8 (a NUL is `C0 80`)
      Lit (LitString str) | all validChar str
                          -> let (cstr,clen) = cstring str
                             in block ("struct { struct kk_bytes_s _base; kk_ssize_t length; uint8_t buf[" <.> int (clen+1) <.> "]; }")
                                      ("{ { { KK_HEADER_STATIC(0,KK_TAG_STRING) } }," <+> int clen <.> "," <+> text cstr <+> "}") "._base._block"
      Inj i t UnitV | isEnum t -> return ([int i],blocks)
      Tuple vs -> foldM (\(ls,bs) v -> do (ls',bs') <- staticLeaves sc bs v
                                          return (ls ++ ls',bs')) ([],blocks) vs
      Ptr _ a -> staticBox sc blocks 0 a
      TyApp v _ -> staticLeaves sc blocks v
      Up v -> staticLeaves sc blocks v
      Down _ v -> staticLeaves sc blocks v
      Some v -> staticLeaves sc blocks v
      Pack _ _ v -> staticLeaves sc blocks v
      _ -> failG ("not a static value: " ++ show val)
  where
    validChar c = c /= '\0' && (c < '\xD800' || c > '\xDFFF')
    found = maybe (failG ("not static: " ++ show val)) (\ls -> return (ls,blocks))
    -- a new static block of a C type with an initialiser, and the member that is its `kk_block_t`
    block decl ini member
      = do let name = text (scBase sc ++ "_value_" ++ show (length blocks))
           return (["((kk_intb_t)&" <.> name <.> member <.> ")"], ("static" <+> decl <+> name <+> "=" <+> ini <.> ";") : blocks)

-- a pointer to a block or a singleton, with the index of the alternative that it is an injection into
staticBox :: SCtx -> [Doc] -> Int -> AVal -> G ([Doc],[Doc])
staticBox sc blocks tag val
  = case val of
      UnitA -> return (["kk_datatype_tag_init(" <.> int (kkTag tag) <.> ")"],blocks)   -- `kk_datatype_from_tag`
      Roll _ v -> staticBox sc blocks tag v
      InjA i _ v -> staticBox sc blocks i v
      InjLazy _ _ v -> staticBox sc blocks tag v
      Box v -> do t <- liftC (inferV (scEnv sc) (scGamma sc) v)
                  ct <- ctype t
                  bt <- blockType ct
                  (ls,blocks') <- staticLeaves sc blocks v
                  payload <- if ct == CUnit then return [] else (:[]) <$> staticInit ct ls
                  let name = text (scBase sc ++ "_value_" ++ show (length blocks'))
                      header = "{ KK_HEADER_STATIC(" <.> int (scanOf ct) <.> "," <.> int (kkTag tag) <.> ") }"
                  return (["((kk_intb_t)&" <.> name <.> "._block)"],
                          ("static" <+> bt <+> name <+> "= {" <+> hcat (punctuate ", " (header : payload)) <+> "};") : blocks')
      _ -> failG ("not a static block: " ++ show val)

-- the initialiser of a value of a C type from the C constants of its leaves
staticInit :: CT -> [Doc] -> G Doc
staticInit ct ls
  = case (ct,ls) of
      (CProd fs,_) | length fs == length ls -> return ("{" <+> hcat (punctuate ", " ["." <.> "f" <.> int i <+> "=" <+> leaf f (ls !! i) | (i,f) <- fs]) <+> "}")
      (CUnit,[]) -> return "kk_Unit"
      (_,[l]) | isLeaf ct -> return (leaf ct l)
      _ -> failG "a static value of this C type"
  where
    leaf CBox l = "{" <+> l <+> "}"
    leaf _ l = l
    isLeaf c = case c of
                 CBox -> True
                 CPrim _ -> True
                 CEnum _ -> True
                 _ -> False

-- modules

cgenModule :: CEnv -> Program -> (String,String,[String])
cgenModule cenv prog
  = let env = envOf prog
        -- (prototype, definition in the header, definition in the C file, initialization)
        genDefE :: M.Map Name Doc -> Def -> G (Either String (Doc,Doc,Doc,Doc))
        genDefE statics d
          | Just ini <- M.lookup (defName d) statics
          = do ct <- ctype (defType d)
               let name = cty ct <+> text (cName (defName d))
               return (Right ("extern" <+> name <.> ";", empty, name <+> "=" <+> ini <.> ";", empty))
        genDefE _ d
          = do st <- get
               case runM (genDef env cenv d) () st{ stLocal = False } of
                 Left err -> return (Left (show (defName d) ++ ": " ++ err))
                 Right ((p,c,i),st') -> do put st'
                                           return (Right (if inHeader d st' then ("static inline" <+> p,"static inline" <+> c,empty,i) else (p,empty,c,i)))
        -- an inline function is defined in the header unless it uses declarations of the C file
        inHeader d st = isInline d && not (stLocal st)
        isInline d@DefFun{} = defInline d == InlineAlways
        isInline DefVal{} = False
        genAll = do statics <- staticValues prog
                    rs <- mapM (genDefE statics) (progDefs prog)
                    ws <- gets (S.toList . stWrappers)
                    wdefs <- mapM (genWrapper env cenv) ws
                    return (rs,wdefs)
    in case runM genAll () (St 0 M.empty [] [] S.empty False) of
         Left err -> ("","",[err])
         Right ((rs,wdefs),st)
           -> let ok    = [x | Right x <- rs]
                  errs  = [e | Left e <- rs]
                  modName = ceModName cenv
                  guardN = text ("KT_" ++ encode (show modName) ++ "_H")
                  initf  = "void" <+> text (ktInitName modName) <.> "(kk_context_t* _ctx)"
                  donef  = "void" <+> text (ktDoneName modName) <.> "(kk_context_t* _ctx)"
                  include h = "#include \"" <.> text h <.> "\""
                  -- `CLayout` writes its definitions as lines that end in a newline
                  layoutDef s = string (init s)
                  ffi = progForeign prog
                  -- the hooks that the foreign C of a module may define (as for Koka's C)
                  hook h = ["#if defined(" <.> h <.> ")", "  " <.> h <.> "(_ctx);", "#endif"]
                  once flag = ["static bool" <+> flag <+> "= false;", "if (" <.> flag <.> ") return;", flag <+> "= true;"]
                  hdr   = vcat (["#ifndef" <+> guardN, "#define" <+> guardN, "#include <kklib.h>", runtimeHeader]
                                ++ [include (modulePath m ++ ".h") | m <- ceImports cenv]
                                ++ map string (forHeader ffi)
                                ++ map string (typeDecls modName prog)
                                ++ [layoutDef (stStructs st M.! n) | n <- stOrder st]
                                ++ [p | (p,_,_,_) <- ok]
                                ++ [h | (_,h,_,_) <- ok]
                                ++ map string (forHeaderEnd ffi)
                                ++ [initf <.> ";", donef <.> ";", "#endif"])
                  csrc  = vcat ([include (modulePath modName ++ ".h")]
                                ++ map string (forSource ffi)
                                ++ map fst wdefs
                                ++ stDecls st
                                ++ [d | (_,_,d,_) <- ok]
                                ++ map snd wdefs
                                ++ [initf <+> block (once "_initialized"
                                                     ++ [text (ktInitName m) <.> "(_ctx);" | m <- ceImports cenv]
                                                     ++ hook "KK_CUSTOM_INIT"
                                                     ++ [i | (_,_,_,i) <- ok, not (isEmptyDoc i)])
                                   ,donef <+> block (once "_done"
                                                     ++ hook "KK_CUSTOM_DONE"
                                                     ++ [text (ktDoneName m) <.> "(_ctx);" | m <- reverse (ceImports cenv)])])
              in (show hdr ++ "\n", show csrc ++ "\n", errs)


-- The C source of the main module of a typed program: its typed C followed by the entry point
-- `mainName`, which initializes the modules (each initializes its imports) and runs `entryName`.
cgenMain :: String -> Int -> Name -> Name -> String
cgenMain mainName stackSize progName entryName
  = unlines (["#include \"" ++ modulePath progName ++ ".c\""]
             ++ ["#include <execinfo.h>"
                ,"#include <stdlib.h>"
                ,"#include <unistd.h>"
                ,"#include <signal.h>"
                ,"static void kt_segv(int sig) { fflush(stdout); void* b[64]; int n = backtrace(b,64); backtrace_symbols_fd(b,n,2); _exit(139); }"
                ,"int " ++ mainName ++ "(int argc, char** argv) {"
                ,"  if (getenv(\"KT_BACKTRACE\") != NULL) { signal(SIGSEGV,&kt_segv); signal(SIGBUS,&kt_segv); }"
                ]
             ++ ["  kk_os_set_stack_size(KK_IZ(" ++ show stackSize ++ "));" | stackSize /= 0]
             ++ ["  kk_context_t* _ctx = kk_main_start(argc, argv);"]
             ++ ["  " ++ ktInitName progName ++ "(_ctx);"
                ,"  " ++ cName entryName ++ "(_ctx);"
                ,"  " ++ ktDoneName progName ++ "(_ctx);"  -- e.g. stops the task threads
                ,"  kk_main_end(_ctx);"
                ,"  return 0;"
                ,"}"])


-- warning pragmas for generated typed C

runtimeHeader :: Doc
runtimeHeader = vcat
  [ "#pragma clang diagnostic ignored \"-Wreturn-type\""
  , "#pragma clang diagnostic ignored \"-Wsometimes-uninitialized\""
  , "#pragma clang diagnostic ignored \"-Wunused-function\""
  , "#pragma clang diagnostic ignored \"-Wshadow\""
  ]
