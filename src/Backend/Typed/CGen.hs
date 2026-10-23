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
  the alternative with index `i` of a sum has tag `i`; unit alternatives are singletons and
  boxes are heap blocks. Externals are called with their Koka C types and their arguments are converted.

  The C code is a `Doc`: string literals are documents, and a list of documents is a list of statements.
-}
module Backend.Typed.CGen( CEnv(..), External(..), cgenModule, runtimeHeader, cName, ktInitName, ktFileName ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char( isAlphaNum, ord, isDigit )
import Data.List( isInfixOf, zip4 )
import Data.Maybe( fromMaybe )
import qualified Numeric
import Control.Monad( forM, when )
import Lib.PPrint( Doc, text, string, int, integer, empty, isEmptyDoc, line, nest, align, vcat, hcat, hsep, (<.>), (<+>), (<->) )
import Common.Name
import Common.NamePrim
import Type.Type
import Kind.Kind( kindStar )
import Kind.Newtypes
import Platform.Runtime( showHFloat )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types( inst, collapse, Types(..) )
import Backend.Typed.Query( Env(..), Gamma, envOf, inferV, inferVar, inferAVar, altTypes, unboxRuGamma, unrollT, openFields, boxContents, reuseSize )
import Backend.Typed.Names( nameLazyFree )
import Backend.Typed.Layout hiding( dupExpr, dropStmt )
import Backend.Typed.Product( productOrder )
import Backend.Typed.Monad

data External = External{ extFormat :: String, extType :: Type }

data CEnv = CEnv{ ceModName   :: Name
                , ceIncludes  :: [String]     -- headers to include
                , ceImportInits :: [String]   -- init functions of imported modules
                , ceExterns   :: M.Map Name External
                , ceNewtypes  :: Newtypes
                , ceDataInfos :: [DataInfo]
                , ceInline    :: S.Set Name   -- small functions defined `static inline` in the header
                , ceEagerLoads :: Bool        -- read the contents of a box at once, not in place (`--feager-loads`)
                }

-- generation monad

-- `stLocal`: whether the current definition uses declarations of the C file (static functions)
data St = St{ stUniq :: Int, stStructs :: M.Map String String, stOrder :: [String], stDecls :: [Doc], stWrappers :: S.Set Name
            , stLocal :: Bool }

-- `cxJoins`: the label and the parameters of each join point in scope
data Ctx = Ctx{ cxEnv :: Env, cxCEnv :: CEnv, cxGamma :: Gamma, cxSelf :: Maybe (Name,[Path])
              , cxJoins :: M.Map Name (Doc,[Path])
              , cxPlaces :: M.Map Path Doc  -- places, read through the pointer to their box (`genUnbox`)
              , cxShared :: S.Set Path     -- boxes known to be shared (the else branch of `IsUnique`)
              , cxSources :: Sources }     -- the copies and join parameters of the definition (`sameBits`)

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

cName :: Name -> String
cName name = "kt_" ++ encode (show name)

localName :: Path -> Doc
localName (Path x ss) = text ("x_" ++ encode (show x) ++ concat ["_p_" ++ encode (show s) | s <- ss])

encode :: String -> String
encode = concatMap enc
  where
    enc c | isAlphaNum c && ord c < 128 = [c]
          | c == '_'  = "__"
          | c == '/'  = "_s_"
          | c == '-'  = "_d_"
          | c == '@'  = "_a_"
          | c == '.'  = "_o_"
          | otherwise = "_x" ++ Numeric.showHex (ord c) "_"

ktFileName :: Name -> String
ktFileName modName = "kt_" ++ encode (show modName)

ktInitName :: Name -> String
ktInitName modName = cName modName ++ "__init"

-- Koka's C names (see Backend.C.FromCore)
kokaName :: Name -> String
kokaName name
  | isQualified name = "kk_" ++ kokaEncode True (show (qualifier name)) ++ "_" ++ asciiEncode False (show (unqualify name))
  | otherwise        = kokaEncode False (show name)
  where
    kokaEncode isModule s = asciiEncode isModule s

kokaTypeName :: Name -> String
kokaTypeName name = kokaName (prependRaw "@" name)

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

-- Like aggregate dup helpers, keep field dups inline: a call can spill another
-- live field and enlarge even the unique path's stack frame. Root dups may be
-- tail calls, so leave their inlining to the C compiler.
dupAt :: Path -> CT -> Doc -> Doc
dupAt x CBox ve | Path _ (_:_) <- canonical x
  = "kt_box_dup_inline(" <.> ve <.> ",_ctx)"
dupAt _ ct ve = dupExpr ct ve

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
      Var x -> genVar cx x
      Glob x _ -> return (text (cName x))
      DupV v -> do t <- tyOf cx v
                   ct <- ctype t
                   e <- genV cx v
                   return (dupExpr ct e)
      UnitV -> return "kk_Unit"
      Lit lit -> genLit lit
      NoReuse _ _ -> return "kk_reuse_null"
      TyApp v _ -> genV cx v
      Ptr _ v -> genA cx v
      Pack _ _ v -> genV cx v
      Inj i t v
        | isEnum t -> do ct <- ctype t
                         return ("((" <.> cty ct <.> ")" <.> int i <.> ")")
        | otherwise
        -> do ct@(CSum name alts) <- ctype t
              let scan = scanOf ct
              x <- fresh "v"
              e <- genV cx v
              let setAlt = case alts !! i of
                             Just _ -> x <.> "._cons.c" <.> int i <+> "=" <+> e <.> ";"
                             Nothing -> empty
              return (stmtExpr ([text name <+> x <.> ";", x <.> "._tag = kk_value_tag(" <.> int (i+1) <.> ");"]
                                ++ [x <.> "._cons._fields[" <.> int j <.> "] = kk_box_null();" | j <- [0..scan-2]]
                                ++ [setAlt]) x)
      Pair _ _ -> do t <- tyOf cx val
                     genProd cx t (prodLeafVals val)
      Hole -> return "kk_box_null()"   -- the placeholder (`kk_cctx_hole`)
      Context b k -> genCtx cx b k
      Plug c v -> genV cx v >>= plug cx c
      Append c d -> genAppend cx c d
      CtxCopy c -> do ct <- tyOf cx c >>= ctype
                      ce <- genV cx c
                      x <- fresh "c"
                      return (stmtExpr [cty ct <+> x <+> "=" <+> ce <.> ";", "kt_ctx_copy(&" <.> x <.> ".f0,&" <.> x <.> ".f1,_ctx);"] x)

-- a context is `res` and the address of its hole; the empty context has neither
genCtx :: Ctx -> AType -> VVal -> G Doc
genCtx cx b k
  = do ct <- tyOf cx (Context b k) >>= ctype
       case k of
         Hole -> makeCtx ct ([],"kk_box_null()","kk_box_null()")
         _ -> genHolePath (bindVar cx nameHole (V (VPtr b))) k >>= makeCtx ct

makeCtx :: CT -> ([Doc],Doc,Doc) -> G Doc
makeCtx ct (ss,res,hole)
  = do x <- fresh "ctx"
       return (stmtExpr (ss ++ [cty ct <+> x <.> ";", x <.> ".f0 =" <+> res <.> ";", x <.> ".f1 =" <+> hole <.> ";"]) x)

-- Appending a nonempty context plugs its `res` into the hole and keeps its hole
-- (`kk_cctx_extend_linear`); otherwise the runtime tests whether the second context is empty.
genAppend :: Ctx -> VVal -> VVal -> G Doc
genAppend cx c d
  = do ct <- tyOf cx (Append c d) >>= ctype
       td <- tyOf cx d
       de <- genV cx d
       case td of
         VCtx Full _ _
           -> do y <- fresh "c"
                 res <- plug cx c (y <.> ".f0")
                 makeCtx ct ([cty ct <+> y <+> "=" <+> de <.> ";"],res,y <.> ".f1")
         _ -> do ce <- genV cx c
                 x <- fresh "c"
                 y <- fresh "c"
                 return (stmtExpr [cty ct <+> x <+> "=" <+> ce <.> ";",
                                   cty ct <+> y <+> "=" <+> de <.> ";",
                                   "kt_ctx_append(&" <.> x <.> ".f0,&" <.> x <.> ".f1," <.> y <.> ".f0," <.> y <.> ".f1,_ctx);"] x)

-- fill the hole of a unique context in place (`kk_cctx_apply_linear`); a copy of a context
-- is filled in place if it is unique and copied with the child otherwise (`kk_cctx_apply`)
plug :: Ctx -> VVal -> Doc -> G Doc
plug cx c ve
  = do let (fill,c') = case c of
                         CtxCopy c0 -> ("kt_ctx_copy_plug",c0)
                         _          -> ("kt_ctx_plug",c)
       ct <- tyOf cx c' >>= ctype
       ce <- genV cx c'
       x <- fresh "c"
       return (stmtExpr [cty ct <+> x <+> "=" <+> ce <.> ";"] (fill <.> "(" <.> x <.> ".f0," <.> x <.> ".f1," <.> ve <.> ",_ctx)"))

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
       let parents = ("kk_datatype_unbox(" <.> r <.> ")") :
                     ["kk_datatype_unbox(((" <.> bt <.> "*)" <.> x <.> ")->" <.> f <.> ")" | (x,(bt,f)) <- zip bs fields]
           steps = ["kk_block_t*" <+> x <+> "= kk_datatype_as_ptr(" <.> parent <.> ",_ctx);" | (x,parent) <- zip bs parents]
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
                      CProd _ _ -> "p.f" <.> int j
                      _ -> "p"
       return (member,inner)
  where
    leaf v i = case v of
                 Hole -> return (i,Nothing)
                 Pair x y | holes x == 1 -> leaf x i
                          | otherwise -> do tx <- tyOf cx x
                                            leaf y (i + length (leaves tx))
                 _ -> return (i,Just v)

-- Injections only contain construction forms, so their tag can be passed down to
-- the allocation; a box or unit outside a sum has tag 1. Existing boxed operands are
-- duplicated through their pointers (`Dup`).
genA :: Ctx -> AVal -> G Doc
genA cx = genAIn cx 1

genAIn :: Ctx -> Int -> AVal -> G Doc
genAIn cx tag val
  = case val of
      Fun f -> staticFun f
      UnitA -> return ("kk_datatype_box(kk_datatype_from_tag((kk_tag_t)" <.> int tag <.> "))")
      Roll _ v -> genAIn cx tag v
      InjA i (ASum _) v -> genAIn cx i v
      InjA _ _ _ -> failG "injection into a non-sum"
      Box v -> genBox cx tag Fresh v
      BoxAt r v -> genBox cx tag (At r) v
      BoxIn x v -> genBox cx tag (In x) v
      Scalar v -> genScalar cx v
      OpenCon c tys vs -> genOpenCon cx c tys vs
      Lam ps r e -> genLam cx ps r e

prodLeafVals :: VVal -> [VVal]
prodLeafVals (Pair v w) = prodLeafVals v ++ prodLeafVals w
prodLeafVals v = [v]

-- construct an unboxed product from values for its components
genProd :: Ctx -> VType -> [VVal] -> G Doc
genProd cx t vs
  = do ct <- ctype t
       case ct of
         CProd name fs
           -> do -- each value covers some leaves
                 parts <- forM vs $ \v -> do tv <- tyOf cx v
                                             e <- genV cx v
                                             return (e, length (leaves tv), tv)
                 x <- fresh "p"
                 assigns <- assignLeaves x (zip [0..] fs) parts 0
                 return (stmtExpr ((text name <+> x <.> ";") : assigns) x)
         _ -> case vs of
                [v] -> genV cx v
                _ -> do es <- mapM (genV cx) vs
                        return (last es)
  where
    assignLeaves x fs [] _ = return []
    assignLeaves x fs ((e,n,s):rest) i
      = do as <- leafAssign x i n s e
           rs <- assignLeaves x fs rest (i+n)
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
         (_,CProd _ _) | n == 1 -> return ("(" <.> e <.> ").f" <.> int start)
         (_,CProd _ _)
           -> do y <- fresh "q"
                 return (stmtExpr ((cty ct <+> y <.> ";") : [y <.> ".f" <.> int j <+> "= (" <.> e <.> ").f" <.> int (start+j) <.> ";" | j <- [0..n-1]]) y)
         _ -> return e

-- where the block of a box comes from
data Alloc = Fresh | At Path | In Path

-- a box: freshly allocated, in the block of a reuse credit, or over the block of a lazy value
-- (whose old fields were taken, see `Lazy`, and whose reference count is kept). A box on the
-- path of a one-hole value records the context path with its header (see `genHolePath`).
genBox :: Ctx -> Int -> Alloc -> VVal -> G Doc
genBox cx tag at v
  = do t <- tyOf cx v
       ct <- ctype t
       e <- genV cx v
       case ct of
         CUnit -> return ("kk_datatype_box(kk_datatype_from_tag((kk_tag_t)" <.> int tag <.> "))")
         _ -> do bt <- blockType ct
                 x <- fresh "b"
                 cpath <- if holes v == 1
                            then do (member,_) <- holeMember cx ct v
                                    return (Just ("(uint8_t)kk_field_index_of(" <.> bt <.> "," <.> member <.> ")"))
                            else return Nothing
                 let scan = int (scanOf ct)
                     path = fromMaybe "0" cpath
                     box  = "kk_datatype_box(kk_datatype_from_base(" <.> x <.> ",_ctx))"
                     allocAt r = "kk_block_alloc_at_as(" <.> bt <.> "," <.> r <.> "," <.> scan <.> "," <.> path <.> ",(kk_tag_t)" <.> int tag <.> ",_ctx)"
                     allocFresh = case cpath of
                                    Nothing -> "kk_block_alloc_as(" <.> bt <.> "," <.> scan <.> ",(kk_tag_t)" <.> int tag <.> ",_ctx)"
                                    Just _ -> allocAt "kk_reuse_null"
                     setPath = maybe empty (\i -> x <.> "->_block.header._field_idx =" <+> i <.> ";") cpath
                 case at of
                   Fresh -> return (stmtExpr [bt <.> "*" <+> x <+> "=" <+> allocFresh <.> ";", x <.> "->p =" <+> e <.> ";"] box)
                   At r  -> do rt <- tyOfName cx r
                               let check = "_Static_assert(sizeof(" <.> bt <.> ") ==" <+> int (blockSize ct) <.> ",\"kt_reuse\");"
                               case rt of
                                 V (VReuse Full _ _)
                                   -> do y <- fresh "reuse_payload"
                                         let field i = case ct of
                                                         CProd _ _ -> ".f" <.> int i
                                                         _ -> empty
                                             writes matches = [x <.> "->p" <.> field i <+> "=" <+> y <.> field i <.> ";"
                                                              | (i,same) <- zip [0..] matches, not same]
                                             setTag k | k == Just tag = empty
                                                      | otherwise = x <.> "->_block.header.tag = (kk_tag_t)" <.> int tag <.> ";"
                                             setScan oldScan | oldScan == scanOf ct = empty
                                                             | otherwise = x <.> "->_block.header.scan_fsize =" <+> int (scanOf ct) <.> ";"
                                             -- A described credit is a unique block of its described payload,
                                             -- so its header only needs the new tag and scan size, where they differ,
                                             -- and only the fields that change are stored. Dups still run, in `y`.
                                             update = case reuseMatches rt t (sameBitsV (cxSources cx) v) of
                                                        Just (k,oldScan,matches) -> [setTag k, setScan oldScan, setPath] ++ writes matches
                                                        Nothing -> ["kk_block_init(&" <.> x <.> "->_block,sizeof(" <.> bt <.> ")," <.> scan <.> "," <.> path <.> ",(kk_tag_t)" <.> int tag <.> ");",
                                                                    x <.> "->p =" <+> y <.> ";"]
                                         return (stmtExpr ([check, cty ct <+> y <+> "=" <+> e <.> ";", bt <.> "*" <+> x <+> "= (" <.> bt <.> "*)" <.> localName r <.> ";"]
                                                           ++ update) box)
                                 -- a credit that may be empty, which `ExpandReuse` did not test
                                 _ -> return (stmtExpr [check, bt <.> "*" <+> x <+> "=" <+> allocAt (localName r) <.> ";", x <.> "->p =" <+> e <.> ";"] box)
                   In y  -> do v <- fresh "v"
                               ye <- genVar cx y
                               let clear = "kt_block_clear(kk_datatype_as_ptr(kk_datatype_unbox(" <.> ye <.> "),_ctx)," <.> scan <.> ",(kk_tag_t)" <.> int tag <.> ",_ctx)"
                               return (stmtExpr [cty ct <+> v <+> "=" <+> e <.> ";", bt <.> "*" <+> x <+> "= (" <.> bt <.> "*)" <.> clear <.> ";",
                                                 setPath, x <.> "->p =" <+> v <.> ";"] box)

-- A projection reads exactly the selected field (`[proj]`), where it is: that of a place
-- binds a place (a sub-place, read at its uses), and that of any other value copies it.
genProjection :: Ctx -> Dest -> VVal -> [Step] -> Path -> VExpr -> G [Doc]
genProjection cx dest v ss x e = do
  t <- tyOf cx v
  (base,pre) <- case v of
    Var z -> do b <- genVar cx z
                return (b,[])
    _ -> do ve <- genV cx v
            z <- fresh "product"
            ct <- ctype t
            return (z,[cty ct <+> z <+> "=" <+> ve <.> ";"])
  (start,u) <- liftC (fieldRange t ss)
  p <- projLeaves t base start u
  case v of
    Var z | M.member z (cxPlaces cx) -> genE (bindPlace cx x u p) dest e
    _ -> do ct <- ctype u
            body <- genE (bindVar cx x (V u)) dest e
            return (pre ++ [declare (cty ct) x p] ++ body)

-- the first leaf and the type of the part at the steps of a projection
fieldRange :: VType -> [Step] -> Either String (Int,VType)
fieldRange t [] = Right (0,t)
fieldRange (VProd a b) (s:ss)
  = case s of
      SFst -> fieldRange a ss
      SSnd -> do (i,u) <- fieldRange b ss
                 return (length (leaves a) + i,u)
      _ -> Left "projection at a non-product step"
fieldRange _ _ = Left "projection of a non-product"

-- The tag and the scan size that the description of a credit records for its block, and for
-- each leaf of the new payload whether its C slot already holds its bits: the old payload has
-- a leaf at the same offset, with the same layout and the same value (`Inline` makes equal
-- values syntactically equal, so the payload names the variables of the description or their
-- copies, `sameBits`).
-- Payloads of different types can thus share slots. A dup preserves a field's bits, but its
-- reference-count effect must still run.
reuseMatches :: Ty -> VType -> VVal -> Maybe (Maybe Int,Int,[Bool])
reuseMatches rt t v
  = case rt of
      V (VReuse _ _ (Just (Contents k old ot)))
        -> let slots s w = zip (leafSlots (layout s)) (leafValues s w)
               kept = slots ot old
           in Just (k, scanOf (layout ot), [leaf `elem` kept | leaf <- slots t v])
      _ -> Nothing

-- The value of each leaf of a value of type `t`, as a value in normal form (`collapse`) and
-- the index of a leaf in it: equal descriptions have equal bits. A variable of a product or
-- existential type is expanded into the variables at its parts. Sums stay whole fields, so
-- their inactive slots are kept safe.
leafValues :: VType -> VVal -> [(VVal,Int)]
leafValues t v
  = case (t,v) of
      (VProd a b, Pair x y) -> leafValues a x ++ leafValues b y
      (VProd a b, Var x) -> leafValues a (Var (child x SFst)) ++ leafValues b (Var (child x SSnd))
      (VExists _ s, Pack _ _ w) -> leafValues s w
      (VExists _ s, Var x) -> leafValues s (Var (child x SPack))
      _ -> [(collapse v,i) | i <- [0 .. length (leaves t) - 1]]

-- `[deref]` and `[unroll]` keep the pointer
genAlias :: Ctx -> Dest -> Doc -> Path -> Ty -> VExpr -> G [Doc]
genAlias cx dest ve x t e
  = do s <- genE (bindVar cx x t) dest e
       return ([declare "kk_box_t" x ve] ++ s)

-- A place stays in its box: it is read at its uses, while the box is alive (Linear), and loaded
-- at `[dup]` and at `[unbox-ru]` (`genUnboxRu`).
genUnbox :: Ctx -> Dest -> Path -> Path -> VExpr -> G [Doc]
genUnbox cx dest v x e
  = do A a <- tyOfName cx v
       t <- liftC (boxContents a)
       ue <- unboxBlock t (localName v)
       if isPlace cx (Unbox Borrowed v x e) x (V t)
         then do ct <- ctype t
                 p <- fresh "payload"
                 s <- genE (bindPlace cx x t ("(*" <.> p <.> ")")) dest e
                 return ((cty ct <.> "*" <+> p <+> "= &(" <.> ue <.> ");") : s)
         else genRead cx dest x t ue e

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

-- Whether a binder of a destructuring is a place (`Layout.placeBinders`). Every read is a
-- load with `--feager-loads`, so that both semantics can be tested.
isPlace :: Ctx -> VExpr -> Path -> Ty -> Bool
isPlace cx e x t = not (ceEagerLoads (cxCEnv cx)) && not (null (placeBinders (`M.member` cxPlaces cx) e [x] [t]))

-- `[unbox-ru]` of `z` takes its block, which may then be freed or written, and renames its
-- contents to `z.taken`. Each part of `z.taken` that the body uses is declared as a local:
-- a place in the block of `z` is loaded, and a local is copied from its old name. The places
-- in the blocks of inner boxes stay places under their new names.
genUnboxRu :: Ctx -> Dest -> Path -> Path -> VExpr -> G [Doc]
genUnboxRu cx dest z r e
  = do g' <- liftC (unboxRuGamma (cxGamma cx) z r)
       let taken = child z STaken
           places = M.fromList [(rebase z p,d) | (p,d) <- M.toList (cxPlaces cx), boxOf p /= Just z]
       locals <- forM [q | q <- S.toList (fvE e), q `within` taken, M.notMember q places] $ \q ->
                   do ct <- liftC (inferVar g' q) >>= ctOf
                      d <- genVar cx (unrebase z q)
                      return (q,declare (cty ct) q d)
       let cx' = cx{ cxGamma = g', cxPlaces = places, cxShared = S.map (rebase z) (cxShared cx) }
       s <- genE cx' dest e
       return (map snd locals ++ [declare "kk_reuse_t" r ("kk_datatype_as_ptr(kk_datatype_unbox(" <.> localName z <.> "),_ctx)")] ++ s)

genVar :: Ctx -> Path -> G Doc
genVar cx x = return (M.findWithDefault (localName x) x (cxPlaces cx))

bindPlace :: Ctx -> Path -> VType -> Doc -> Ctx
bindPlace cx x t d = let cx' = bindVar cx x (V t) in cx'{ cxPlaces = M.insert x d (cxPlaces cx') }

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

-- the payload of a box, which is never the dummy value of a yield (`[let-yield]`)
unboxBlock :: VType -> Doc -> G Doc
unboxBlock t e
  = do ct <- ctype t
       case ct of
         CUnit -> return "kk_Unit"
         _ -> do bt <- blockType ct
                 return ("((" <.> bt <.> "*)kk_datatype_as_ptr(kk_datatype_unbox(" <.> e <.> "),_ctx))->p")

-- The dummy value of a yield: Koka's `box-any` in every pointer, which the runtime may drop
-- (`kcompose`), as `kk_valuetype_unbox_from_any` makes it.
yieldedValue :: CT -> G Doc
yieldedValue ct
  = case ct of
      CUnit -> return "kk_Unit"
      CBox -> return "kk_box_any(_ctx)"
      _ -> do x <- fresh "yd"
              return (stmtExpr [cty ct <+> x <+> "= {0};",
                                "kk_valuetype_unbox_from_any((kk_box_t*)&" <.> x <.> ",sizeof(" <.> cty ct <.> "),kk_box_any(_ctx),KK_OWNED,_ctx);"] x)

-- literals

genLit :: Lit -> G Doc
genLit lit
  = case lit of
      LitInt i | i >= -8191 && i <= 8191 -> return ("kt_box_integer(kk_integer_from_small(" <.> integer i <.> "))")
               | i >= -2147483647 && i <= 2147483647 -> return ("kt_box_integer(kk_integer_from_int(" <.> integer i <.> ",_ctx))")
               | otherwise -> return ("kt_box_integer(kk_integer_from_str(\"" <.> integer i <.> "\",_ctx))")
      LitFloat d -> return (text (showHFloat d ""))
      LitChar c -> return ("((kk_char_t)" <.> int (fromEnum c) <.> ")")
      LitString "" -> return "kt_box_string(kk_string_empty())"
      LitString s -> do x <- fresh "s"
                        let (cstr,clen) = cstring s
                        return (stmtExpr ["kk_define_string_literal(static," <.> x <.> "," <.> int clen <.> "," <.> text cstr <.> ",_ctx);"]
                                         ("kt_box_string(kk_string_dup(" <.> x <.> ",_ctx))"))

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
       let fields = [(i,capCts !! i) | i <- productOrder (map (capType . snd) capTys)]
           capType (V t) = t
           capType (A a) = VPtr a
           scan   = 1 + sum (map (scanOf . snd) fields)
       n <- freshName "lam"
       let sname = "struct kt_clo" <.> text n
           fname = "kt_fun" <.> text n
       pcts <- mapM (\(_,_,t) -> ctype t) ps
       rct  <- ctype r
       let structDef = sname <+> block ("struct kk_function_s _base;" : [cty ct <+> "c" <.> int i <.> ";" | (i,ct) <- fields]) <.> ";"
           g'  = M.union (M.fromList ([(x,V t) | (x,_,t) <- ps])) (cxGamma cx)
           cx' = cx{ cxGamma = g', cxSelf = Nothing, cxJoins = M.empty }
       body <- genE cx'{ cxPlaces = M.empty } DReturn e
       -- Transfer captures from unique closures; shared closures retain their own references.
       let loads = [cty ct <+> localName (caps !! i) <+> "= _self->c" <.> int i <.> ";" | (i,ct) <- fields]
           dups = [x <+> "=" <+> dupExpr ct x <.> ";" | (i,ct) <- fields, needsRC ct, let x = localName (caps !! i)]
           sig = "static" <+> cty rct <+> fname <.> "(kk_function_t _fself" <.> hcat [", " <.> cty ct <+> localName x | ((x,_,_),ct) <- zip ps pcts] <.> ", kk_context_t* _ctx)"
           prologue | null caps = ["kk_function_static_drop(_fself,_ctx);"]
                    | otherwise = (sname <.> "* _self = kk_function_as(" <.> sname <.> "*,_fself,_ctx);") : loads
                                  ++ ["kk_drop_match(_self,{" <+> hsep dups <+> "},{},_ctx);"]
       emitDecl (vcat ([structDef | not (null caps)] ++ [sig <+> block (prologue ++ body)]))
       x <- fresh "c"
       capVals <- mapM (genVar cx) caps
       -- A capture-free closure can share a static function block.
       if null caps
         then return (stmtExpr ["kk_define_static_function(" <.> x <.> "," <.> fname <.> ",_ctx);"]
                               ("kk_datatype_box(kk_function_static_dup(" <.> x <.> ",_ctx))"))
         else return (stmtExpr ([sname <.> "*" <+> x <+> "= kk_function_alloc_as(" <.> sname <.> "," <.> int scan <.> ",_ctx);",
                                 x <.> "->_base.fun = kk_kkfun_ptr_box(&" <.> fname <.> ",_ctx);"]
                                ++ [x <.> "->c" <.> int i <+> "=" <+> (capVals !! i) <.> ";" | (i,_) <- fields])
                               ("kk_datatype_box(kk_datatype_from_base(&" <.> x <.> "->_base,_ctx))"))

lamFree :: [(Path,Mode,VType)] -> VExpr -> S.Set Path
lamFree ps e = fvA (Lam ps VUnit e)

-- open datatypes use the constructors of Koka's headers
genOpenCon :: Ctx -> Name -> [AType] -> [VVal] -> G Doc
genOpenCon cx c tys vs
  = do (fields,kfields) <- openConFields cx c tys
       args <- forM (zip3 vs fields kfields) $ \(v,f,kt) ->
                 do e <- genV cx v
                    fct <- ctype f
                    return (toKoka fct (kokaCType kt) e)
       let new = text (kokaName (makeHiddenName "new" c))
       return ("kt_box_datatype(" <.> new <.> "(" <.> (if null args then empty else "kk_reuse_null,0,") <.> hcat [a <.> "," | a <- args] <.> "_ctx))")

-- the fields of an open constructor at type arguments, with their Koka types
openConFields :: Ctx -> Name -> [AType] -> G ([VType],[Type])
openConFields cx c tys
  = case M.lookup c (envSigs (cxEnv cx)) of
      Just (SigCon _ _ n) ->
        do ci <- conInfoOf cx c
           fields <- liftC (openFields (cxEnv cx) c (ACon n tys))
           return (fields, map snd (conInfoParams ci))
      _ -> failG ("unknown open constructor " ++ show c)

conInfoOf :: Ctx -> Name -> G ConInfo
conInfoOf cx c
  = case [ci | di <- ceDataInfos (cxCEnv cx), ci <- dataInfoConstrs di, conInfoName ci == c] of
      (ci:_) -> return ci
      [] -> failG ("unknown constructor " ++ show c)

-- conversions between our C types and Koka's C types

kokaCType :: Type -> String
kokaCType tp
  = case tp of
      TForall _ t -> kokaCType t
      TFun _ _ _ -> "kk_function_t"
      TApp t _ -> kokaCType t
      TVar _ -> "kk_box_t"
      TSyn _ _ t -> kokaCType t
      TCon c -> let n = typeConName c
                in maybe (kokaTypeName n) id (lookup n kokaPrimTypes)

kokaPrimTypes :: [(Name,String)]
kokaPrimTypes
  = [(nameTpInt,"kk_integer_t"),(nameTpString,"kk_string_t"),(nameTpBytes,"kk_bytes_t"),(nameTpVector,"kk_vector_t")
    ,(nameTpEvv,"kk_evv_t"),(nameTpChar,"kk_char_t"),(nameTpSSizeT,"kk_ssize_t"),(nameTpIntPtrT,"intptr_t")
    ,(nameTpFloat,"double"),(nameTpBool,"bool"),(nameTpUnit,"kk_unit_t"),(nameTpInt64,"int64_t"),(nameTpByte,"uint8_t")
    ,(nameTpInt8,"int8_t"),(nameTpInt16,"int16_t"),(nameTpInt32,"int32_t"),(nameTpMarker,"int32_t")
    ,(nameTpFloat32,"float"),(nameTpFloat16,"float"),(nameTpRef,"kk_ref_t"),(nameTpLocalVar,"kk_ref_t")
    ,(nameTpBox,"kk_box_t"),(nameTpAny,"kk_box_t"),(nameTpReuse,"kk_reuse_t"),(nameTpFieldAddr,"kk_field_addr_t")]

toKoka :: CT -> String -> Doc -> Doc
toKoka ct kt e
  | ctName ct == kt = e
  | otherwise
  = case ct of
      CEnum _ -> "((" <.> text kt <.> ")(" <.> e <.> "))"
      CPrim _ -> "((" <.> text kt <.> ")(" <.> e <.> "))"
      _ -> "kt_pun(" <.> text kt <.> "," <.> e <.> ")"

fromKoka :: String -> CT -> Doc -> Doc
fromKoka kt ct e
  | ctName ct == kt = e
  | otherwise
  = case ct of
      CEnum _ -> "((" <.> cty ct <.> ")(" <.> e <.> "))"
      CPrim _ -> "((" <.> cty ct <.> ")(" <.> e <.> "))"
      _ -> "kt_pun(" <.> cty ct <.> "," <.> e <.> ")"

-- expressions

data Dest = DReturn | DAssign Doc | DDiscard

assignTo :: Dest -> CT -> Doc -> [Doc]
assignTo dest ct e
  = case dest of
      DReturn   -> ["return" <+> e <.> ";"]
      DAssign x -> [x <+> "=" <+> e <.> ";"]
      DDiscard  -> ["(void)(" <.> e <.> ");"]

bindVar :: Ctx -> Path -> Ty -> Ctx
bindVar cx x t = cx{ cxGamma = M.insert x t (cxGamma cx), cxPlaces = M.delete x (cxPlaces cx) }

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
      Let x t e1 e2
        -> do s1 <- genBound cx x t e1
              s2 <- genE (bindVar cx x (V t)) dest e2
              return (s1 ++ s2)
      LetYield x t e1 e2 e3
        -> do s1 <- genBound cx x t e1
              s2 <- genE (bindVar cx x (V t)) dest e2
              s3 <- genE cx dest e3
              return (s1 ++ [ifChain [("kk_yielding(_ctx)",s3)] s2])
      Yielded t
        -> do ct <- ctype t
              e <- yieldedValue ct
              return (assignTo dest ct e)
      Drop x e
        | S.member x (cxShared cx)   -- like Koka's C backend: a shared block only needs a decrement
        -> do s <- genE cx dest e
              return (["kk_block_decref(kk_datatype_as_ptr(kk_datatype_unbox(" <.> localName x <.> "),_ctx),_ctx);"] ++ s)
        | otherwise
        -> do t <- tyOfName cx x
              ve <- genVar cx x
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
      Dup x y e
        -> do t <- tyOfName cx x
              ct <- ctOf t
              ve <- genVar cx x
              s <- genE (bindVar cx y t) dest e
              return (declare (cty ct) y (dupAt x ct ve) : s)
      IsUnique x e1 e2
        -> do t <- liftC (inferVar (cxGamma cx) x)
              s1 <- genE cx dest e1
              xe <- genVar cx x
              let d = "kk_datatype_unbox(" <.> xe <.> ")"
                  (test,shared) = case t of
                    V _ -> ("kk_datatype_is_unique(" <.> d <.> ",_ctx)", cxShared cx)   -- a lazy value may be immediate
                    A _ -> ("kk_block_is_unique(kk_datatype_as_ptr(" <.> d <.> ",_ctx))", S.insert x (cxShared cx))
              s2 <- genE cx{ cxShared = shared } dest e2
              return ["if kk_likely(" <.> test <.> ")" <+> block s1 <+> "else" <+> block s2]
      IfFull r e1 e2
        -> do t <- liftC (inferVar (cxGamma cx) r)
              full <- case t of
                        V (VReuse _ n p) -> return (V (VReuse Full n p))
                        _ -> failG ("test of a non-credit: " ++ show r)
              s1 <- genE (bindVar cx r full) dest e1
              s2 <- genE cx dest e2
              return ["if kk_likely(" <.> localName r <+> "!= kk_reuse_null)" <+> block s1 <+> "else" <+> block s2]
      UnboxRu v r e -> genUnboxRu cx dest v r e
      Gen _ e -> genE cx dest e
      Join j _ ps e1 e2
        -> do lbl <- fresh "join"
              decls <- mapM (\(x,_,t) -> do ct <- ctype t
                                            return (cty ct <+> localName x <.> ";")) ps
              s2 <- genE cx{ cxJoins = M.insert j (lbl,[x | (x,_,_) <- ps]) (cxJoins cx) } dest e2
              s1 <- genE (foldl (\c (x,_,t) -> bindVar c x (V t)) cx ps) dest e1
              let (skip,end) = case dest of
                                 DReturn -> ([],[])
                                 _ -> (["goto" <+> lbl <.> "_end;"], [lbl <.> "_end: ;"])
              return [block (decls ++ s2 ++ skip ++ [lbl <.> ":" <+> block s1] ++ end)]
      Jump j _ vs
        -> do (lbl,xs) <- maybe (failG ("jump to unknown join point " ++ show j)) return (M.lookup j (cxJoins cx))
              args <- mapM (genV cx) vs
              return ([localName x <+> "=" <+> a <.> ";" | (x,a) <- zip xs args] ++ ["goto" <+> lbl <.> ";"])
      Call f tys vs -> genCall cx dest f tys vs
      App f vs
        -> do ft <- tyOfName cx f
              (ps,r) <- case ft of
                          A (AFun ps r) -> return (map snd ps, r)
                          _ -> failG ("application of " ++ show ft)
              pcts <- mapM ctype ps
              rct  <- ctype r
              args <- mapM (genV cx) vs
              fx <- fresh "fn"
              let call = "kk_function_call(" <.> cty rct <.> ",(kk_function_t" <.> hcat [", " <.> cty ct | ct <- pcts] <.> ", kk_context_t*),"
                         <.> fx <.> ",(" <.> fx <.> hcat [", " <.> a | a <- args] <.> ", _ctx),_ctx)"
              return [block (("kk_function_t" <+> fx <+> "= kk_datatype_unbox(" <.> localName f <.> ");") : assignTo dest rct call)]
      Proj _ v ss x e -> genProjection cx dest v ss x e
      Unpack _ v tvs x e
        -> do VExists bs body <- tyOf cx v
              let t = inst bs (map AVar tvs) body
              ve <- genV cx v
              if isPlace cx expr x (V t)
                then genE (bindPlace cx x t ve) dest e
                else genRead cx dest x t ve e
      Deref _ v x e
        -> do VPtr a <- tyOf cx v
              ve <- genV cx v
              genAlias cx dest ve x (A a) e
      Unroll _ v x e
        -> do A t <- tyOfName cx v
              a <- liftC (unrollT (cxEnv cx) t)
              genAlias cx dest (localName v) x (A a) e
      Unbox _ v x e -> genUnbox cx dest v x e
      -- Lazy contents are taken as owned roots; they must survive freeing the
      -- lazy block even though their paths no longer name parts of that block.
      UnboxLazy v x e
        -> do A a <- tyOfName cx v
              t <- liftC (boxContents a)
              ue <- unboxBlock t (localName v)
              genRead cx dest x t ue e
      Unscalar m v x e -> genUnscalar cx dest m v x e
      SplitA _ v k (x,e1) (y,e2)
        -> do t <- tyOfName cx v
              [[tl@(A ls)],[tr@(A rs)]] <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
              left <- genSumBranch cx dest v x tl e1
              right <- genSumBranch cx dest v y tr e2
              tg <- fresh "t"
              let (header,test) = case pointerTest ve ls rs of
                                   Just c -> ([],c)
                                   Nothing -> ([tagDecl t tg ve],tg <+> "<" <+> int k)
              return [block (header ++ [ifChain [(test,left)] right])]
      CaseA _ v alts def
        -> do t <- tyOfName cx v
              tss <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
              brs <- forM (zip alts tss) $ \((i,x,e),ts) -> do
                [ti] <- return ts
                body <- genSumBranch cx dest v x ti e
                return ([i],body)
              fallback <- case (def, drop (length alts) tss) of
                            (Just (x,e), [[td]]) -> Just <$> genSumBranch cx dest v x td e
                            _ -> return Nothing
              tg <- fresh "t"
              -- Match owns partitioning. Only a single alternative with a
              -- default needs an equality branch.
              let dispatch = case (brs,fallback) of
                    ([([tag],body)],Just other) -> ifChain [(tg <+> "==" <+> int tag,body)] other
                    _ -> switchCases tg brs fallback
              return [block [tagDecl t tg ve, dispatch]]
      CaseV _ v alts
        -> do t@(VSum ts) <- tyOf cx v
              ct <- ctype t
              ve <- genV cx v
              z <- fresh "w"
              brs <- forM (zip3 [0..] ts alts) $ \(i,ti,(x,e)) ->
                       do cti <- ctype ti
                          let payload = case ct of
                                CSum _ alts' | Just _ <- alts' !! i -> z <.> "._cons.c" <.> int i
                                _ -> "kk_Unit"
                          body <- genE (bindVar cx x (V ti)) dest e
                          return ([i], declare (cty cti) x payload : body)
              let tag = case ct of { CEnum _ -> z; _ -> "kk_smallint_from_integer(" <.> z <.> "._tag) - 1" }
                  dispatch = case brs of
                    [(_,body)] -> body
                    [(_,left),(_,right)] -> [ifChain [("(" <.> tag <.> ") == 0",left)] right]
                    _ -> [switchCases tag brs (Just ["kt_unreachable();"])]
              return [block ((cty ct <+> z <+> "=" <+> ve <.> ";") : dispatch)]
      CaseLit v alts def
        -> do tv <- tyOf cx v
              ve <- genV cx v
              brs <- forM alts $ \(l,e) ->
                       do s <- genE cx dest e
                          return (litTest ve l, s)
              sd <- genE cx dest def
              return [ifChain brs sd]
      CaseOpen _ v alts def
        -> do let ve = localName v
              brs <- forM alts $ \(c,xs,e) ->
                       do tys <- openTypeArgs cx v
                          (fields,kfields) <- openConFields cx c tys
                          names <- conFieldNames cx c
                          let acc n = text (kokaName (makeHiddenName "as" c)) <.> "(kt_unbox_datatype(" <.> ve <.> "),_ctx)->" <.> text n
                          decls <- forM (zip4 xs fields kfields names) $ \(x,f,kt,n) ->
                                     do fct <- ctype f
                                        return (declare (cty fct) x (fromKoka (kokaCType kt) fct (acc n)))
                          s <- genE (foldl (\cx' (x,f) -> bindVar cx' x (V f)) cx (zip xs fields)) dest e
                          let tag = text (kokaName (makeHiddenName "tag" c))
                          return ("kt_open_is(" <.> ve <.> "," <.> tag <.> ",_ctx)", decls ++ s)
              sd <- genE cx dest def
              return [ifChain brs sd]

-- declare the binder of a `let` and assign it the value of the bound expression
genBound :: Ctx -> Path -> VType -> VExpr -> G [Doc]
genBound cx x t e
  = do ct <- ctype t
       s <- genE cx (DAssign (localName x)) e
       -- the binders of `e` are out of scope in the body, and a path may be bound in both
       let assign = case e of
                      Ret _ -> s
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
tagDecl t tg ve = "kk_tag_t" <+> tg <+> "=" <+> tagRead <.> ";"
  where
    d = "kk_datatype_unbox(" <.> ve <.> ")"
    tagRead = case t of
                A a | shapeIsHeap a == Just True -> "kk_block_tag(kk_datatype_as_ptr(" <.> d <.> ",_ctx))"
                _ -> "kk_datatype_tag(" <.> d <.> ",_ctx)"

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
  where
    intLit i | i >= -8191 && i <= 8191 = "kk_integer_from_small(" <.> integer i <.> ")"
             | otherwise = "kk_integer_from_str(\"" <.> integer i <.> "\",_ctx)"

openTypeArgs :: Ctx -> Path -> G [AType]
openTypeArgs cx v
  = do t <- tyOfName cx v
       case t of
         A (ACon _ args) -> return args
         _ -> return []

conFieldNames :: Ctx -> Name -> G [String]
conFieldNames cx c
  = do ci <- conInfoOf cx c
       return [kokaLocal (unqualify n) | (n,_) <- conInfoParams ci]

kokaLocal :: Name -> String
kokaLocal n
  = let s = asciiEncode False (show n)
    in if take 3 s == "kk_" || null s || isDigit (head s) || s `elem` cReserved then "kkloc_" ++ s else s

cReserved :: [String]
cReserved = ["bool","toString","arguments","eval","char","int","intptr_t","long","short","signed","size_t","ssize_t","intptr_t","uintptr_t","unsigned","uint8_t","double","auto","extern","float","goto","inline","restrict","sizeof","static","volatile","async","await","break","case","catch","class","continue","const","debugger","default","delete","do","else","finally","for","function","if","in","instanceof","new","return","register","switch","struct","this","throw","try","typeof","typedef","union","var","void","while","with","yield","class","enum","export","extends","import","super","errno","exception_info","or","timezone"]

-- calls

genCall :: Ctx -> Dest -> Name -> [AType] -> [VVal] -> G [Doc]
genCall cx dest f tys vs
  | f == nameLazyFree, [v] <- vs
  = do e <- genV cx v
       return (("kk_block_free(kk_datatype_as_ptr(kk_datatype_unbox(" <.> e <.> "),_ctx),_ctx);") : assignTo dest CUnit "kk_Unit")
  | [Lit (LitInt i)] <- vs, Just (kt,lit) <- fixedWidthLit f i
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       return (assignTo dest rct (fromKoka kt rct lit))
  | Just (v,i,neq) <- smallIntComparison f vs
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       e <- genV cx v
       let arg = "kt_unbox_integer(" <.> e <.> ")"
           test = case i of
                    0  -> "kk_integer_is_zero_borrow(" <.> arg <.> ")"
                    1  -> "kk_integer_is_one_borrow(" <.> arg <.> ")"
                    -1 -> "kk_integer_is_minus_one_borrow(" <.> arg <.> ")"
                    _  -> "kk_integer_eq_borrow(kk_integer_from_small(" <.> integer i <.> ")," <.> arg <.> ",_ctx)"
       return (assignTo dest rct (fromKoka "bool" rct (if neq then "!(" <.> test <.> ")" else test)))
  | Just (v,i) <- smallIntArithmetic f vs
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       e <- genV cx v
       let call = "kk_integer_add_small_const(kt_unbox_integer(" <.> e <.> ")," <.> integer i <.> ",_ctx)"
       return (assignTo dest rct (fromKoka "kk_integer_t" rct call))
  | Just ext <- M.lookup f (ceExterns (cxCEnv cx)) = genExtern cx dest f tys vs ext
  | otherwise
  = do (ps,r) <- callSig cx f tys
       rct <- ctype r
       args <- mapM (genV cx) vs
       case (dest, cxSelf cx) of
         (DReturn, Just (self,params)) | self == f && length params == length args
           -> do tmps <- mapM (const (fresh "a")) args
                 pcts <- mapM ctype ps
                 return [block ([cty ct <+> t <+> "=" <+> a <.> ";" | (t,a,ct) <- zip3 tmps args pcts]
                                ++ [localName p <+> "=" <+> t <.> ";" | (p,t) <- zip params tmps]
                                ++ ["goto kt_tailcall;"])]
         _ -> return (assignTo dest rct (callName f <.> "(" <.> hcat [a <.> ", " | a <- args] <.> "_ctx)"))

-- A small constant cannot equal a bigint. Put it first for the general equality
-- helper, whose fast rejection tests its first operand; common values have predicates.
smallIntComparison :: Name -> [VVal] -> Maybe (VVal,Integer,Bool)
smallIntComparison f vs
  | f `elem` [eq,neq]
  = do (v,i) <- case vs of
                  [v,Lit (LitInt i)] | isSmallInt i -> Just (v,i)
                  [Lit (LitInt i),v] | isSmallInt i -> Just (v,i)
                  _ -> Nothing
       return (v,i,f == neq)
  | otherwise = Nothing
  where
    eq  = newQualified "std/core/int" "=="
    neq = newQualified "std/core/int" "!="

isSmallInt :: Integer -> Bool
isSmallInt i = i >= -8192 && i <= 8191

-- Keep the signed increment small on every target, including after negating
-- a subtraction constant. The runtime helper still handles big integers and overflow.
smallIntArithmetic :: Name -> [VVal] -> Maybe (VVal,Integer)
smallIntArithmetic f vs
  = do (v,i) <- case vs of
                  [v,Lit (LitInt i)] | f == nameIntAdd -> Just (v,i)
                  [Lit (LitInt i),v] | f == nameIntAdd -> Just (v,i)
                  [v,Lit (LitInt i)] | f == nameIntSub -> Just (v,-i)
                  _ -> Nothing
       if isSmallInt i then Just (v,i) else Nothing

-- Conversions of small integer literals to fixed-width integers become C literals
-- (as in `Backend.C.FromCore.genAppSpecial`); `ssize_t` and `intptr_t` stay within 32 bits
-- so that they fit on every platform.
fixedWidthLit :: Name -> Integer -> Maybe (String,Doc)
fixedWidthLit f i
  | f `elem` [nameInt32,nameInternalInt32] && within 31 = Just ("int32_t", "KK_I32(" <.> integer i <.> ")")
  | f == nameInt64 && within 63                         = Just ("int64_t", "KK_I64(" <.> integer i <.> ")")
  | f `elem` [nameSSizeT,nameInternalSSizeT] && within 31 = Just ("kk_ssize_t", "KK_IZ(" <.> integer i <.> ")")
  | f == nameIntPtrT && within 31                       = Just ("intptr_t", "KK_IP(" <.> integer i <.> ")")
  | f == nameByte && i >= 0 && i <= 255                 = Just ("uint8_t", "((uint8_t)" <.> integer i <.> ")")
  | otherwise = Nothing
  where
    within bits = abs i < 2^bits   -- excludes the minimum, which is not a valid C literal

callName :: Name -> Doc
callName f
  | f == newHiddenName "typed-unreachable" = "kt_unreachable_value"
  | otherwise = text (cName f)

callSig :: Ctx -> Name -> [AType] -> G ([VType],VType)
callSig cx f tys
  = case M.lookup f (envSigs (cxEnv cx)) of
      Just (SigFun tvs ps r) -> return (map (inst tvs tys . snd) ps, inst tvs tys r)
      _ -> failG ("unknown function " ++ show f)

genExtern :: Ctx -> Dest -> Name -> [AType] -> [VVal] -> External -> G [Doc]
genExtern cx dest f tys vs ext
  = do (ps,r) <- callSig cx f tys
       let (kpars,kres) = kokaFunType (extType ext)
       rct <- ctype r
       args <- forM (zip3 vs ps (kpars ++ repeat (TVar (TypeVar 0 kindStar Bound)))) $ \(v,p,kp) ->
                 do e <- genV cx v
                    ct <- ctype p
                    return (toKoka ct (externCType kp p) e, externCType kp p)
       let fmt   = extFormat ext
           named = [(n,a) | (n,a) <- zip (kokaParamNames (extType ext)) args, n `elem` cIdents fmt]
           call | isComment fmt = empty
                | null named    = substFormat fmt (map fst args)
                | otherwise     = stmtExpr [text kt <+> text n <+> "=" <+> a <.> ";" | (n,(a,kt)) <- named]  -- parameters used by name
                                           (substFormat fmt (map fst args))
       case r of
         VUnit | isEmptyDoc call -> return (assignTo dest CUnit "kk_Unit")
         VUnit -> return (("(void)(" <.> call <.> ");") : assignTo dest CUnit "kk_Unit")
         _ -> return (assignTo dest rct (fromKoka (externCType kres r) rct call))
  where
    -- Koka passes type variables of its lazy internals at their instance (see `Backend.C.Box`)
    externCType kt t
      = case (kt,t) of
          (TVar _, VPtr (ACon n _)) | f `elem` unboxedInternals -> maybe (kokaTypeName n) id (lookup n kokaPrimTypes)
          _ -> kokaCType kt

unboxedInternals :: [Name]
unboxedInternals
  = [nameLazyMemoizeTarget, nameLazyMemoize, nameLazyEnter, nameLazyLeave, nameLazyIsWhnf, nameLazyPtrIsWhnf
    ,nameDataTypePtrIsThreadShared, nameDataTypePtrIsUnique, nameLazyIndirectCompress]

kokaFunType :: Type -> ([Type],Type)
kokaFunType tp
  = case tp of
      TForall _ t -> kokaFunType t
      TSyn _ _ t -> kokaFunType t
      TFun ps _ r -> (map snd ps, r)
      _ -> ([],tp)

-- the identifiers in a piece of C code
cIdents :: String -> [String]
cIdents s = case dropWhile (not . isIdent) s of
              "" -> []
              s' -> let (w,rest) = span isIdent s' in w : cIdents rest
  where isIdent c = isAlphaNum c || c == '_'

kokaParamNames :: Type -> [String]
kokaParamNames tp
  = case tp of
      TForall _ t -> kokaParamNames t
      TSyn _ _ t  -> kokaParamNames t
      TFun ps _ _ -> [show n | (n,_) <- ps]
      _           -> []

isComment :: String -> Bool
isComment fmt = case dropWhile (== ' ') fmt of
                  ('/':'*':_) -> True
                  ""          -> True
                  _           -> False

substFormat :: String -> [Doc] -> Doc
substFormat fmt args = go fmt
  where
    go [] = empty
    go ('\\':'#':xs) = "#" <.> go xs
    go ('#':d:xs) | isDigit d && d /= '0' = let i = fromEnum d - fromEnum '1'
                                            in (if i < length args then "(" <.> args !! i <.> ")" else "/*missing*/") <.> go xs
    -- Raw C newlines must not add indentation inside backslash-continued strings.
    go (x:xs) = text [x] <.> go xs

-- definitions

genDef :: Env -> CEnv -> Def -> G (Doc,Doc,Doc)
genDef env cenv def
  = case def of
      DefFun f _ args res body
        -> do pcts <- mapM (\(_,_,t) -> ctype t) args
              rct  <- ctype res
              let g  = M.fromList [(x,V t) | (x,_,t) <- args]
                  cx = Ctx env cenv g (Just (f,[x | (x,_,_) <- args])) M.empty M.empty S.empty (sources body)
              ss <- genE cx DReturn body
              let sig = cty rct <+> text (cName f) <.> "(" <.> hcat [cty ct <+> localName x <.> ", " | ((x,_,_),ct) <- zip args pcts] <.> "kk_context_t* _ctx)"
                  label = ["kt_tailcall: ;" | "goto kt_tailcall;" `isInfixOf` show (vcat ss)]
              return (sig <.> ";", sig <+> block (label ++ ss), empty)
      DefVal x _ t body
        -> do ct <- ctype t
              let cx = Ctx env cenv M.empty Nothing M.empty M.empty S.empty (sources body)
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
      Just (SigFun tvs ps r)
        -> do pcts <- mapM (ctype . snd) ps
              rct  <- ctype r
              let xs  = [root (newHiddenName ("p" ++ show i)) | i <- [0..length ps - 1]]
                  cx  = Ctx env cenv (M.fromList [(x,V t) | (x,(_,t)) <- zip xs ps]) Nothing M.empty M.empty S.empty M.empty
              body <- genCall cx DReturn f (map AVar tvs) (map Var xs)
              let sig = "static" <+> cty rct <+> text (cName f) <.> "_fun(kk_function_t _fself" <.> hcat [", " <.> cty ct <+> localName x | (x,ct) <- zip xs pcts] <.> ", kk_context_t* _ctx)"
              return (sig <.> ";", sig <+> block ("kk_function_static_drop(_fself,_ctx);" : body))
      _ -> failG ("wrapper for unknown function " ++ show f)

-- modules

cgenModule :: CEnv -> Program -> (String,String,[String])
cgenModule cenv prog
  = let env = envOf prog
        -- (prototype, definition in the header, definition in the C file, initialization)
        genDefE :: Def -> G (Either String (Doc,Doc,Doc,Doc))
        genDefE d = do st <- get
                       case runM (genDef env cenv d) () st{ stLocal = False } of
                         Left err -> return (Left (show (defName d) ++ ": " ++ err))
                         Right ((p,c,i),st') -> do put st'
                                                   return (Right (if inHeader d st' then ("static inline" <+> p,"static inline" <+> c,empty,i) else (p,empty,c,i)))
        -- a small function is defined in the header unless it uses declarations of the C file
        inHeader d st = S.member (defName d) (ceInline cenv) && isFun d && not (stLocal st)
        isFun DefFun{} = True
        isFun DefVal{} = False
        genAll = do rs <- mapM genDefE (progDefs prog)
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
                  include h = "#include \"" <.> text h <.> "\""
                  -- `Layout` writes its definitions as lines that end in a newline
                  layoutDef s = string (init s)
                  hdr   = vcat (["#ifndef" <+> guardN, "#define" <+> guardN]
                                ++ map include (take 1 (ceIncludes cenv))
                                ++ [runtimeHeader]
                                ++ map include (drop 1 (ceIncludes cenv))
                                ++ [layoutDef (stStructs st M.! n) | n <- stOrder st]
                                ++ [p | (p,_,_,_) <- ok]
                                ++ [h | (_,h,_,_) <- ok]
                                ++ [initf <.> ";", "#endif"])
                  csrc  = vcat ([include (take (length h - 2) h ++ ".c") | h <- take 1 (ceIncludes cenv)]
                                ++ [include (ktFileName modName ++ ".h")]
                                ++ map fst wdefs
                                ++ stDecls st
                                ++ [d | (_,_,d,_) <- ok]
                                ++ map snd wdefs
                                ++ [initf <+> block (["static bool _initialized = false;", "if (_initialized) return;", "_initialized = true;"]
                                                     ++ [text i <.> "(_ctx);" | i <- ceImportInits cenv]
                                                     ++ [i | (_,_,_,i) <- ok])])
              in (show hdr ++ "\n", show csrc ++ "\n", errs)


-- runtime support

runtimeHeader :: Doc
runtimeHeader = vcat
  [ "#ifndef KT_RUNTIME_H"
  , "#define KT_RUNTIME_H"
  , "#include <string.h>"
  , "#pragma clang diagnostic ignored \"-Wreturn-type\""
  , "#pragma clang diagnostic ignored \"-Wsometimes-uninitialized\""
  , "#pragma clang diagnostic ignored \"-Wunused-function\""
  , "#pragma clang diagnostic ignored \"-Wshadow\""
  , "#define kt_pun(T,x) ({ __typeof__(x) _kt_x = (x); T _kt_y; _Static_assert(sizeof(T)==sizeof(_kt_x),\"kt_pun\"); memcpy(&_kt_y,&_kt_x,sizeof(T)); _kt_y; })"
  , "#define kt_box_integer(i)  kt_pun(kk_box_t,i)"
  , "#define kt_unbox_integer(b) kt_pun(kk_integer_t,b)"
  , "#define kt_box_string(s)   kt_pun(kk_box_t,s)"
  , "#define kt_unbox_string(b) kt_pun(kk_string_t,b)"
  , "#define kt_box_datatype(d) kk_datatype_box(d)"
  , "#define kt_unbox_datatype(b) kk_datatype_unbox(b)"
  , "#define kt_unreachable() kk_fatal_error(EFAULT,\"typed backend: unreachable\")"
  , "#define kt_unreachable_value(ctx) (kt_unreachable(), kk_box_null())"
  , "static inline __attribute__((always_inline)) kk_box_t kt_box_dup_inline(kk_box_t b, kk_context_t* ctx) {"
  , "  return kk_box_dup(b,ctx);"
  , "}"
  , "// plug the hole of a unique context (`kk_cctx_apply_linear`); an empty context has no hole"
  , "static inline kk_box_t kt_ctx_plug(kk_box_t res, kk_box_t hole, kk_box_t child, kk_context_t* _ctx) {"
  , "  if kk_likely(!kk_box_eq(hole,kk_box_null())) {"
  , "    kk_assert_internal(kk_block_is_unique(kk_ptr_unbox(res,_ctx)));"
  , "    *kk_internal_ptr_unbox(hole,_ctx) = child;"
  , "    return res;"
  , "  }"
  , "  return child;"
  , "}"
  , "// append a unique context to a unique one: plug its `res` into the hole and keep its hole"
  , "static inline void kt_ctx_append(kk_box_t* res, kk_box_t* hole, kk_box_t res2, kk_box_t hole2, kk_context_t* _ctx) {"
  , "  if (!kk_box_eq(hole2,kk_box_null())) { *res = kt_ctx_plug(*res,*hole,res2,_ctx); *hole = hole2; }"
  , "}"
  , "// copy the path of a shared context (`kk_cctx_copy`), which consumes the shared `res`"
  , "static inline void kt_ctx_copy(kk_box_t* res, kk_box_t* hole, kk_context_t* _ctx) {"
  , "  if (!kk_box_eq(*hole,kk_box_null()) && !kk_block_is_unique(kk_ptr_unbox(*res,_ctx))) {"
  , "    kk_box_t* h = NULL;"
  , "    *res = kk_cctx_copy(*res,kk_internal_ptr_unbox(*hole,_ctx),&h,_ctx);"
  , "    *hole = kk_internal_ptr_box(h,_ctx);"
  , "  }"
  , "}"
  , "// plug the hole of a context that may be shared (`kk_cctx_apply`): copy its path if it is"
  , "static inline kk_box_t kt_ctx_copy_plug(kk_box_t res, kk_box_t hole, kk_box_t child, kk_context_t* _ctx) {"
  , "  if kk_unlikely(kk_box_eq(hole,kk_box_null())) return child;"
  , "  if kk_likely(kk_block_is_unique(kk_ptr_unbox(res,_ctx))) {"
  , "    *kk_internal_ptr_unbox(hole,_ctx) = child;"
  , "    return res;"
  , "  }"
  , "  return kk_cctx_copy_apply(res,kk_internal_ptr_unbox(hole,_ctx),child,_ctx);"
  , "}"
  , "static inline kk_block_t* kt_block_clear(kk_block_t* b, kk_ssize_t scan_fsize, kk_tag_t tag, kk_context_t* _ctx) {"
  , "  b->header.scan_fsize = (uint8_t)scan_fsize; b->header.tag = tag;"
  , "  return b;"
  , "}"
  , "// credits come from box blocks, which are always allocated with `kk_malloc_small`"
  , "static inline void kt_reuse_drop(kk_reuse_t r, kk_context_t* _ctx) {"
  , "  if (r != kk_reuse_null) { kk_assert_internal(kk_block_is_unique(r)); kk_free_small(r,_ctx); }"
  , "}"
  , "static inline void kt_reuse_free(kk_reuse_t r, kk_context_t* _ctx) {"
  , "  kk_assert_internal(r != kk_reuse_null && kk_block_is_unique(r)); kk_free_small(r,_ctx);"
  , "}"
  , "static inline bool kt_open_is(kk_box_t b, kk_string_t tag, kk_context_t* _ctx) {"
  , "  struct kt_open_s { kk_block_t _block; kk_string_t _tag; };"
  , "  return kk_string_ptr_eq_borrow(((struct kt_open_s*)kk_datatype_as_ptr(kk_datatype_unbox(b),_ctx))->_tag, tag);"
  , "}"
  , "#endif"
  ]
