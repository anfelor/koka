-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- C code generation from the typed IR (after Perceus).

  Unboxed types are represented as described in `Layout`. A boxed sum is a `kk_box_t`:
  alternative `i` of a datatype has tag `i+1`; unit alternatives are singletons and boxes
  are heap blocks. Externals are called with their Koka C types and their arguments are converted.
-}
module Backend.Typed.CGen( CEnv(..), External(..), cgenModule, runtimeHeader, cName, ktInitName, ktFileName ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char( isAlphaNum, ord, isDigit )
import Data.List( isInfixOf )
import Data.Maybe( fromMaybe )
import qualified Numeric
import Control.Monad( forM, when )
import Common.Name
import Common.NamePrim
import Type.Type
import Kind.Kind( kindStar )
import Kind.Newtypes
import Platform.Runtime( showHFloat )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types( inst, prodV, sumWidth, Types(..) )
import Backend.Typed.Query( Env(..), Gamma, envOf, inferV, inferVar, inferAVar, altTypes, unboxRuBinds, unrollT, openFields, boxContents, reuseSize, contentsOfAlt, contentsValueOfAlt )
import Backend.Typed.Names( nameLazyFree )
import Backend.Typed.Layout
import Backend.Typed.Monad

data External = External{ extFormat :: String, extType :: Type }

data CEnv = CEnv{ ceModName   :: Name
                , ceIncludes  :: [String]     -- headers to include
                , ceImportInits :: [String]   -- init functions of imported modules
                , ceExterns   :: M.Map Name External
                , ceNewtypes  :: Newtypes
                , ceDataInfos :: [DataInfo]
                , ceInline    :: S.Set Name   -- small functions defined `static inline` in the header
                }

-- generation monad

-- `stLocal`: whether the current definition uses declarations of the C file (static functions)
data St = St{ stUniq :: Int, stStructs :: M.Map String String, stOrder :: [String], stDecls :: [String], stWrappers :: S.Set Name
            , stLocal :: Bool }

-- `cxJoins`: the label and the parameters of each join point in scope
-- `cxValues`: expanded, allocation-free values used only for payload comparison
-- `cxAliases` and `cxPayloads`: pointer identities and projected payloads for RC cancellation
data Ctx = Ctx{ cxEnv :: Env, cxCEnv :: CEnv, cxGamma :: Gamma, cxNamed :: S.Set Name, cxSelf :: Maybe (Name,[Name])
              , cxJoins :: M.Map Name (String,[Name]), cxValues :: M.Map Name VVal
              , cxAliases :: M.Map Name Name, cxPayloads :: M.Map Name VVal
              , cxShared :: S.Set Name }   -- boxes known to be shared (the else branch of `IsUnique`)

type G a = M () St a

failG :: String -> G a
failG = fail

liftC :: Either String a -> G a
liftC = liftE

fresh :: String -> G String
fresh s = state (\st -> ("_" ++ s ++ show (stUniq st), st{ stUniq = stUniq st + 1 }))

emitDecl :: String -> G ()
emitDecl d = modify (\st -> st{ stDecls = stDecls st ++ [d], stLocal = True })

-- names

cName :: Name -> String
cName name = "kt_" ++ encode (show name)

localName :: Name -> String
localName name = "x_" ++ encode (show name)

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
blockType :: CT -> G String
blockType ct
  = do uncurry defineStruct (blockDef ct)
       return ("struct " ++ blockName ct)

-- types of values

tyOf :: Ctx -> VVal -> G VType
tyOf cx v = liftC (inferV (cxEnv cx) (cxGamma cx) v)

tyOfName :: Ctx -> Name -> G Ty
tyOfName cx x = liftC (inferVar (cxGamma cx) x)

ctOf :: Ty -> G CT
ctOf (V t) = ctype t
ctOf (A _) = return CBox

-- Translate a binary shape decision using the pointer bit when it identifies
-- the two sides; otherwise the decision uses their tag intervals.
pointerTest :: String -> AType -> AType -> Maybe String
pointerTest ve left right
  = case (shapeIsHeap left,shapeIsHeap right) of
      (Just l,Just r) | l /= r -> Just ((if l then "" else "!") ++ "kk_datatype_is_ptr(kk_datatype_unbox(" ++ ve ++ "))")
      _ -> Nothing

-- size of a boxed sum
sumSize :: AType -> Int
sumSize = sumWidth

-- values

genV :: Ctx -> VVal -> G String
genV cx val
  = case val of
      Var x -> return (localName x)
      Glob x _ -> return (cName x)
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
                         return ("((" ++ ctName ct ++ ")" ++ show i ++ ")")
        | otherwise
        -> do ct@(CSum name alts) <- ctype t
              let scan = scanOf ct
              x <- fresh "v"
              e <- genV cx v
              let setAlt = case alts !! i of
                             Just _ -> x ++ "._cons.c" ++ show i ++ " = " ++ e ++ "; "
                             Nothing -> ""
              return ("({ " ++ name ++ " " ++ x ++ "; " ++ x ++ "._tag = kk_value_tag(" ++ show (i+1) ++ "); "
                      ++ concat [x ++ "._cons._fields[" ++ show j ++ "] = kk_box_null(); " | j <- [0..scan-2]]
                      ++ setAlt ++ x ++ "; })")
      Pair _ _ -> do t <- tyOf cx val
                     genProd cx t (prodLeafVals val)
      Hole -> return "kk_box_null()"   -- the placeholder (`kk_cctx_hole`)
      Context b k -> genCtx cx b k
      Plug c v -> genV cx v >>= plug cx c
      Append c d -> genAppend cx c d
      CtxCopy c -> do ct <- tyOf cx c >>= ctype
                      ce <- genV cx c
                      x <- fresh "c"
                      return ("({ " ++ ctName ct ++ " " ++ x ++ " = " ++ ce ++ "; kt_ctx_copy(&" ++ x ++ ".f0,&" ++ x ++ ".f1,_ctx); " ++ x ++ "; })")

-- a context is `res` and the address of its hole; the empty context has neither
genCtx :: Ctx -> AType -> VVal -> G String
genCtx cx b k
  = do ct <- tyOf cx (Context b k) >>= ctype
       case k of
         Hole -> makeCtx ct ([],"kk_box_null()","kk_box_null()")
         _ -> genHolePath (bindVar cx nameHole (V (VPtr b))) k >>= makeCtx ct

makeCtx :: CT -> ([String],String,String) -> G String
makeCtx ct (ss,res,hole)
  = do x <- fresh "ctx"
       return ("({ " ++ concat ss ++ ctName ct ++ " " ++ x ++ "; " ++ x ++ ".f0 = " ++ res ++ "; " ++ x ++ ".f1 = " ++ hole ++ "; " ++ x ++ "; })")

-- Appending a fresh context that is not empty plugs its `res` into the hole and keeps its hole
-- (`kk_cctx_extend_linear`); otherwise the runtime tests whether the second context is empty.
genAppend :: Ctx -> VVal -> VVal -> G String
genAppend cx c d
  = do ct <- tyOf cx (Append c d) >>= ctype
       case d of
         Context b k | k /= Hole
           -> do (ss,r,h) <- genHolePath (bindVar cx nameHole (V (VPtr b))) k
                 res <- plug cx c r
                 makeCtx ct (ss,res,h)
         _ -> do ce <- genV cx c
                 de <- genV cx d
                 x <- fresh "c"
                 y <- fresh "c"
                 return ("({ " ++ ctName ct ++ " " ++ x ++ " = " ++ ce ++ "; " ++ ctName ct ++ " " ++ y ++ " = " ++ de ++ "; "
                         ++ "kt_ctx_append(&" ++ x ++ ".f0,&" ++ x ++ ".f1," ++ y ++ ".f0," ++ y ++ ".f1,_ctx); " ++ x ++ "; })")

-- fill the hole of a unique context in place (`kk_cctx_apply_linear`); a copy of a context
-- is filled in place if it is unique and copied with the child otherwise (`kk_cctx_apply`)
plug :: Ctx -> VVal -> String -> G String
plug cx c ve
  = do let (fill,c') = case c of
                         CtxCopy c0 -> ("kt_ctx_copy_plug",c0)
                         _          -> ("kt_ctx_plug",c)
       ct <- tyOf cx c' >>= ctype
       ce <- genV cx c'
       x <- fresh "c"
       return ("({ " ++ ctName ct ++ " " ++ x ++ " = " ++ ce ++ "; " ++ fill ++ "(" ++ x ++ ".f0," ++ x ++ ".f1," ++ ve ++ ",_ctx); })")

-- Allocate a one-hole value (`genBox` records the context path in the header of each block on
-- the path to the hole): the statements, `res` and the address of the hole (`kk_field_addr_t`).
-- The address is bound before the context is used, as in `kk_cctx_extend_linear`.
genHolePath :: Ctx -> VVal -> G ([String],String,String)
genHolePath cx k
  = do r <- fresh "r"
       h <- fresh "h"
       ke <- genV cx k
       fields <- pathFields k
       bs <- mapM (const (fresh "b")) fields
       let parents = ("kk_datatype_unbox(" ++ r ++ ")") :
                     ["kk_datatype_unbox(((" ++ bt ++ "*)" ++ x ++ ")->" ++ f ++ ")" | (x,(bt,f)) <- zip bs fields]
           steps = ["kk_block_t* " ++ x ++ " = kk_datatype_as_ptr(" ++ parent ++ ",_ctx); " | (x,parent) <- zip bs parents]
           (bt,f) = last fields
           hole = "kk_box_t " ++ h ++ " = kk_internal_ptr_box(&((" ++ bt ++ "*)" ++ last bs ++ ")->" ++ f ++ ",_ctx); "
       return (("kk_box_t " ++ r ++ " = " ++ ke ++ "; ") : steps ++ [hole], r, h)
  where
    -- the type of each block on the path, and the member that leads to the hole
    pathFields v = case v of
                     Ptr _ a -> block a
                     _ -> failG ("not a one-hole value: " ++ show v)
    block a = case a of
                Roll _ w -> block w
                InjA _ _ w -> block w
                Box v -> payload v
                BoxAt _ v -> payload v
                _ -> failG ("not a one-hole value: " ++ show a)
    payload v = do ct <- tyOf cx v >>= ctype
                   bt <- blockType ct
                   (member,inner) <- holeMember cx ct v
                   rest <- maybe (return []) pathFields inner
                   return ((bt,member) : rest)

-- the member of a payload that leads to the hole, and the nested one-hole value there
holeMember :: Ctx -> CT -> VVal -> G (String,Maybe VVal)
holeMember cx ct v
  = do (j,inner) <- leaf v 0
       let member = case ct of
                      CProd _ _ -> "p.f" ++ show j
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
-- the allocation. Existing boxed operands are duplicated by the expression `Dup`.
genA :: Ctx -> AVal -> G String
genA cx = genAIn cx False 0

genAIn :: Ctx -> Bool -> Int -> AVal -> G String
genAIn cx inSum pos val
  = case val of
      Fun f -> staticFun f
      UnitA -> return ("kk_datatype_box(kk_datatype_from_tag((kk_tag_t)" ++ show (pos+1) ++ "))")
      Roll _ v -> genAIn cx inSum pos v
      InjA i (ASum _) v -> genAIn cx True (pos + i) v
      InjA _ _ _ -> failG "injection into a non-sum"
      Box v -> genBox cx inSum (pos+1) Fresh v
      BoxAt r v -> genBox cx inSum (pos+1) (At r) v
      BoxIn x v -> genBox cx inSum (pos+1) (In x) v
      OpenCon c tys v -> genOpenCon cx c tys v
      Lam ps r e -> genLam cx ps r e

prodLeafVals :: VVal -> [VVal]
prodLeafVals (Pair v w) = prodLeafVals v ++ prodLeafVals w
prodLeafVals v = [v]

-- construct an unboxed product from values for its components
genProd :: Ctx -> VType -> [VVal] -> G String
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
                 return ("({ " ++ name ++ " " ++ x ++ "; " ++ concat assigns ++ x ++ "; })")
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
      | n == 0 = return ["(void)(" ++ e ++ "); "]
      | n == 1 = return [x ++ ".f" ++ show i ++ " = " ++ e ++ "; "]
      | otherwise = do sct <- ctype s
                       y <- fresh "q"
                       let sname = ctName sct
                       return ([sname ++ " " ++ y ++ " = " ++ e ++ "; "] ++
                               [x ++ ".f" ++ show (i+j) ++ " = " ++ y ++ ".f" ++ show j ++ "; " | j <- [0..n-1]])

-- project a component (a range of leaves) from a product
projLeaves :: VType -> String -> Int -> VType -> G String
projLeaves whole e start part
  = do let n = length (leaves part)
       ct <- ctype part
       wct <- ctype whole
       case (n, wct) of
         (0,_) -> return "kk_Unit"
         (_,CProd _ _) | n == 1 -> return ("(" ++ e ++ ").f" ++ show start)
         (_,CProd _ _)
           -> do let pname = ctName ct
                 y <- fresh "q"
                 return ("({ " ++ pname ++ " " ++ y ++ "; " ++ concat [y ++ ".f" ++ show j ++ " = (" ++ e ++ ").f" ++ show (start+j) ++ "; " | j <- [0..n-1]] ++ y ++ "; })")
         _ -> return e

-- where the block of a box comes from
data Alloc = Fresh | At Name | In Name

-- a box: freshly allocated, in the block of a reuse credit, or over the block of a lazy value
-- (whose old fields were taken, see `Lazy`, and whose reference count is kept). A box on the
-- path of a one-hole value records the context path with its header (see `genHolePath`).
genBox :: Ctx -> Bool -> Int -> Alloc -> VVal -> G String
genBox cx inSum tag at v
  = do t <- tyOf cx v
       ct <- ctype t
       e <- genV cx v
       case ct of
         CPrim p | not inSum, Just (box,_) <- primBox p -> return (box ++ "(" ++ e ++ ",_ctx)")
         CEnum _ | not inSum -> return ("kk_int32_box((int32_t)" ++ e ++ ",_ctx)")
         CUnit -> return ("kk_datatype_box(kk_datatype_from_tag((kk_tag_t)" ++ show tag ++ "))")
         _ -> do bt <- blockType ct
                 x <- fresh "b"
                 cpath <- if holes v == 1
                            then do (member,_) <- holeMember cx ct v
                                    return (Just ("(uint8_t)kk_field_index_of(" ++ bt ++ "," ++ member ++ ")"))
                            else return Nothing
                 let scan = show (scanOf ct)
                     box  = "kk_datatype_box(kk_datatype_from_base(" ++ x ++ ",_ctx)); })"
                     allocAt r = "kk_block_alloc_at_as(" ++ bt ++ "," ++ r ++ "," ++ scan ++ "," ++ fromMaybe "0" cpath ++ ",(kk_tag_t)" ++ show tag ++ ",_ctx)"
                     allocFresh = case cpath of
                                    Nothing -> "kk_block_alloc_as(" ++ bt ++ "," ++ scan ++ ",(kk_tag_t)" ++ show tag ++ ",_ctx)"
                                    Just _ -> allocAt "kk_reuse_null"
                     setPath = maybe "" (\i -> x ++ "->_block.header._field_idx = " ++ i ++ "; ") cpath
                 case at of
                   Fresh -> return ("({ " ++ bt ++ "* " ++ x ++ " = " ++ allocFresh ++ "; "
                                    ++ x ++ "->p = " ++ e ++ "; " ++ box)
                   At r  -> do described <- reuseMatches cx r t v
                               let matches = maybe [] snd described
                                   alloc = allocAt (localName r)
                                   start = "({ _Static_assert(sizeof(" ++ bt ++ ") == " ++ show (blockSize ct) ++ ",\"kt_reuse\"); "
                                   saved = length (filter id matches)
                                   setTag | creditTag cx r == Just tag = ""
                                          | otherwise = x ++ "->_block.header.tag = (kk_tag_t)" ++ show tag ++ "; "
                                   setScan | fmap fst described == Just (scanOf ct) = ""
                                           | otherwise = x ++ "->_block.header.scan_fsize = " ++ show (scanOf ct) ++ "; "
                               if saved < 1 + ((1 + length matches) `div` 4)
                                 then return (start ++ bt ++ "* " ++ x ++ " = " ++ alloc ++ "; " ++ x ++ "->p = " ++ e ++ "; " ++ box)
                                 else do y <- fresh "reuse_payload"
                                         let field i = case ct of
                                                         CProd _ _ -> ".f" ++ show i
                                                         _ -> ""
                                             writes = concat [x ++ "->p" ++ field i ++ " = " ++ y ++ field i ++ "; "
                                                             | (i,same) <- zip [0..] matches, not same]
                                         -- Evaluate once before testing the credit: dups still run
                                         -- even when their corresponding stores are omitted.
                                         -- A described credit is a unique block of its described payload,
                                         -- so its header only needs the new tag and scan size, where they differ.
                                         return (start ++ ctName ct ++ " " ++ y ++ " = " ++ e ++ "; " ++ bt ++ "* " ++ x ++ "; "
                                                 ++ "if kk_likely(" ++ localName r ++ " != kk_reuse_null) { "
                                                 ++ x ++ " = (" ++ bt ++ "*)" ++ localName r ++ "; " ++ setTag ++ setScan ++ setPath ++ writes
                                                 ++ "} else { " ++ x ++ " = " ++ allocFresh ++ "; "
                                                 ++ x ++ "->p = " ++ y ++ "; } " ++ box)
                   In y  -> do v <- fresh "v"
                               return ("({ " ++ ctName ct ++ " " ++ v ++ " = " ++ e ++ "; "
                                       ++ bt ++ "* " ++ x ++ " = (" ++ bt ++ "*)kt_block_clear(kk_datatype_as_ptr(kk_datatype_unbox(" ++ localName y ++ "),_ctx)," ++ scan ++ ",(kk_tag_t)" ++ show tag ++ ",_ctx); "
                                       ++ setPath ++ x ++ "->p = " ++ v ++ "; " ++ box)

-- The credit's old payload layout (by its scan size) and, for each leaf of the new payload,
-- whether its C slot already holds its bits: the old payload has a leaf at the same offset,
-- with the same layout and the same value. Payloads of different types can thus share
-- slots. A dup preserves a field's bits, but its reference-count effect must still run.
-- Sums are treated as whole fields so their inactive/padding slots are kept safe.
reuseMatches :: Ctx -> Name -> VType -> VVal -> G (Maybe (Int,[Bool]))
reuseMatches cx r t v
  = do rt <- tyOfName cx r
       case rt of
         V (VReuse _ (Just (Contents _ old ot)))
           -> do oct <- ctype ot
                 ct <- ctype t
                 let slots s w ctw = zip (leafSlots ctw) (leafValues s (replaceV (cxValues cx) w))
                     kept = slots ot old oct
                 return (Just (scanOf oct, [leaf `elem` kept | leaf <- slots t v ct]))
         _ -> return Nothing

-- the tag that the description of a credit records in the header of its block
-- (see `genAIn` for the tags of boxes)
creditTag :: Ctx -> Name -> Maybe Int
creditTag cx r
  = case M.lookup r (cxGamma cx) of
      Just (V (VReuse _ (Just (Contents k _ _)))) -> Just k
      _ -> Nothing

-- The value of each leaf of a value of type `t`, as a value and the index of a leaf in it:
-- equal descriptions have equal bits.
leafValues :: VType -> VVal -> [(VVal,Int)]
leafValues t v
  = case (t,v) of
      (_, DupV w) -> leafValues t w
      (VProd a b, Pair x y) -> leafValues a x ++ leafValues b y
      (VExists _ s, Pack _ _ w) -> leafValues s w
      _ -> [(v,i) | i <- [0 .. length (leaves t) - 1]]

-- Expose the same fields in credit contents and saved aggregate descriptions.
-- A scrutinee that renames another aggregate exposes that aggregate's fields too.
contentsCtx :: Ctx -> VExpr -> Ty -> Int -> [Name] -> Ctx
contentsCtx cx expr t i xs = cx{ cxGamma = contentsOfAlt expr t i xs (cxGamma cx)
                             , cxValues = renamed (M.map refine (cxValues cx)), cxPayloads = M.map refine (cxPayloads cx) }
  where refine = contentsValueOfAlt expr t i xs
        renamed values = case fmap dsScrut (destructVOf expr) of
                           Just s@(Var x) | Just (Var w) <- M.lookup x (cxValues cx) -> M.insert w (refine s) values
                           _ -> values

-- `[deref]`, `[unroll]` and `[dup-a]` keep the pointer
genAlias :: Ctx -> Dest -> String -> Maybe Name -> Name -> Ty -> S.Set Name -> VExpr -> G [String]
genAlias cx dest ve source x t named e
  = do s <- genE (aliasCtx cx source x (bindVar cx{ cxNamed = named } x t)) dest e
       return (["kk_box_t " ++ localName x ++ " = " ++ ve ++ ";"] ++ s)

genUnbox :: Bool -> Ctx -> Dest -> Name -> Name -> VExpr -> G [String]
genUnbox track cx dest v x e
  = do tv@(A (ABox t)) <- tyOfName cx v
       let ve = localName v
           inSum = position tv /= Whole
       ct <- ctype t
       let -- Scalar unbox helpers can consume the box themselves. For immediate
           -- scalars this removes the generic drop; heap-backed scalars still
           -- release their storage through the runtime's owned unbox path.
           scalar = case ct of
                      CPrim p -> case primBox p of { Just _ -> True; _ -> False }
                      CEnum _ -> True
                      _       -> False
           (mode,body) = case e of
                           Drop z rest | z == v, scalar, not inSum -> (Owned,rest)
                           _ -> (Borrowed,e)
       ue <- unboxV cx mode inSum (S.member v (cxNamed cx)) t ve
       let cx' = (bindVar cx x (V t)){ cxPayloads = if track then M.insert (aliasRoot cx v) (Var x) (cxPayloads cx) else M.empty }
       s <- genE cx' dest body
       return ([ctName ct ++ " " ++ localName x ++ " = " ++ ue ++ ";"] ++ s)

-- the payload of a box; only a box at a type variable can be Koka's `box-any`
unboxV :: Ctx -> Mode -> Bool -> Bool -> VType -> String -> G String
unboxV cx mode inSum named t e
  = do ct <- ctype t
       let borrow = if owning mode then "KK_OWNED" else "KK_BORROWED"
       case ct of
         CPrim p | not inSum, Just (_,unbox) <- primBox p -> return (unbox ++ "(" ++ e ++ "," ++ borrow ++ ",_ctx)")
         CEnum _ | not inSum -> return ("(" ++ ctName ct ++ ")kk_int32_unbox(" ++ e ++ "," ++ borrow ++ ",_ctx)")
         CUnit -> return "kk_Unit"
         _ -> do bt <- blockType ct
                 x <- fresh "ub"
                 y <- fresh "ux"
                 let read = "((" ++ bt ++ "*)kk_datatype_as_ptr(kk_datatype_unbox(" ++ e ++ "),_ctx))->p"
                 if named then return read else
                  return ("({ kk_box_t " ++ y ++ " = " ++ e ++ "; " ++ ctName ct ++ " " ++ x ++ "; if kk_unlikely(kt_box_is_any(" ++ y ++ ",_ctx)) { kk_valuetype_unbox_from_any((kk_box_t*)&" ++ x ++ ",sizeof(" ++ ctName ct ++ ")," ++ y ++ ",KK_BORROWED,_ctx); } else { " ++ x ++ " = ((" ++ bt ++ "*)kk_datatype_as_ptr(kk_datatype_unbox(" ++ y ++ "),_ctx))->p; } " ++ x ++ "; })")

-- literals

genLit :: Lit -> G String
genLit lit
  = case lit of
      LitInt i | i >= -8191 && i <= 8191 -> return ("kt_box_integer(kk_integer_from_small(" ++ show i ++ "))")
               | i >= -2147483647 && i <= 2147483647 -> return ("kt_box_integer(kk_integer_from_int(" ++ show i ++ ",_ctx))")
               | otherwise -> return ("kt_box_integer(kk_integer_from_str(\"" ++ show i ++ "\",_ctx))")
      LitFloat d -> return (showHFloat d "")
      LitChar c -> return ("((kk_char_t)" ++ show (fromEnum c) ++ ")")
      LitString "" -> return "kt_box_string(kk_string_empty())"
      LitString s -> do x <- fresh "s"
                        let (cstr,clen) = cstring s
                        return ("({ kk_define_string_literal(static," ++ x ++ "," ++ show clen ++ "," ++ cstr ++ ",_ctx); kt_box_string(kk_string_dup(" ++ x ++ ",_ctx)); })")

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
staticFun :: Name -> G String
staticFun f
  = do modify (\st -> st{ stWrappers = S.insert f (stWrappers st), stLocal = True })
       x <- fresh "f"
       return ("({ kk_define_static_function(" ++ x ++ "," ++ cName f ++ "_fun,_ctx); kk_datatype_box(" ++ x ++ "); })")

-- closures
genLam :: Ctx -> [(Name,Mode,VType)] -> VType -> VExpr -> G String
genLam cx ps r e
  = do let caps = S.toList (lamFree ps e)
       capTys <- mapM (\x -> case M.lookup x (cxGamma cx) of
                               Just t -> return (x,t)
                               Nothing -> failG ("unbound captured variable " ++ show x)) caps
       capCts <- mapM (ctOf . snd) capTys
       let fields = orderFields (zip [0..] capCts)
           scan   = 1 + sum (map (scanOf . snd) fields)
       n <- fresh "lam"
       let sname = "struct kt_clo" ++ n
           fname = "kt_fun" ++ n
       pcts <- mapM (\(_,_,t) -> ctype t) ps
       rct  <- ctype r
       let structDef = sname ++ " { struct kk_function_s _base; " ++ concat [ctName ct ++ " c" ++ show i ++ "; " | (i,ct) <- fields] ++ "};\n"
           g'  = M.union (M.fromList ([(x,V t) | (x,_,t) <- ps])) (cxGamma cx)
           cx' = cx{ cxGamma = g', cxSelf = Nothing, cxJoins = M.empty, cxValues = M.empty, cxAliases = M.empty, cxPayloads = M.empty }
       body <- genE cx' DReturn e
       -- Transfer captures from unique closures; shared closures retain their own references.
       let loads = [ctName ct ++ " " ++ localName (caps !! i) ++ " = _self->c" ++ show i ++ ";" | (i,ct) <- fields]
           dups = [x ++ " = " ++ dupExpr ct x ++ ";" | (i,ct) <- fields, needsRC ct, let x = localName (caps !! i)]
           fun = "static " ++ ctName rct ++ " " ++ fname ++ "(kk_function_t _fself" ++ concat [", " ++ ctName ct ++ " " ++ localName x | ((x,_,_),ct) <- zip ps pcts] ++ ", kk_context_t* _ctx) {\n"
                 ++ (if null caps then "  kk_function_static_drop(_fself,_ctx);\n"
                     else "  " ++ sname ++ "* _self = kk_function_as(" ++ sname ++ "*,_fself,_ctx);\n" ++ concatMap (\l -> "  " ++ l ++ "\n") loads
                          ++ "  kk_drop_match(_self,{ " ++ unwords dups ++ " },{},_ctx);\n")
                 ++ indent body ++ "}\n"
       emitDecl ((if null caps then "" else structDef) ++ fun)
       x <- fresh "c"
       -- A capture-free closure can share a static function block.
       if null caps
         then return ("({ kk_define_static_function(" ++ x ++ "," ++ fname ++ ",_ctx); "
                      ++ "kk_datatype_box(kk_function_static_dup(" ++ x ++ ",_ctx)); })")
         else return ("({ " ++ sname ++ "* " ++ x ++ " = kk_function_alloc_as(" ++ sname ++ "," ++ show scan ++ ",_ctx); "
                      ++ x ++ "->_base.fun = kk_kkfun_ptr_box(&" ++ fname ++ ",_ctx); "
                      ++ concat [x ++ "->c" ++ show i ++ " = " ++ localName (caps !! i) ++ "; " | (i,_) <- fields]
                      ++ "kk_datatype_box(kk_datatype_from_base(&" ++ x ++ "->_base,_ctx)); })")

lamFree :: [(Name,Mode,VType)] -> VExpr -> S.Set Name
lamFree ps e = fvA (Lam ps VUnit e)

-- open datatypes use the constructors of Koka's headers
genOpenCon :: Ctx -> Name -> [AType] -> VVal -> G String
genOpenCon cx c tys v
  = do (fields,kfields) <- openConFields cx c tys
       e <- genV cx v
       x <- fresh "o"
       let ft = prodV fields
       args <- forM (zip3 [0..] fields kfields) $ \(i,f,kt) ->
                 do p <- projLeaves ft x (sum (map (length . leaves) (take i fields))) f
                    fct <- ctype f
                    return (toKoka fct (kokaCType kt) p)
       fct <- ctype ft
       return ("({ " ++ ctName fct ++ " " ++ x ++ " = " ++ e ++ "; kt_box_datatype(" ++ kokaName (makeHiddenName "new" c) ++ "(" ++ (if null args then "" else "kk_reuse_null,0,") ++ concatMap (++ ",") args ++ "_ctx)); })")

openConFields :: Ctx -> Name -> [AType] -> G ([VType],[Type])
openConFields cx c tys
  = case M.lookup c (envSigs (cxEnv cx)) of
      Just (SigCon tvs f _) ->
        do let fs = inst tvs tys f
           ktypes <- conKokaFields cx c
           return (fieldsOf (length ktypes) fs, ktypes)
      _ -> failG ("unknown open constructor " ++ show c)
  where
    fieldsOf 0 _ = []
    fieldsOf 1 t = [t]
    fieldsOf n (VProd a b) = a : fieldsOf (n-1) b
    fieldsOf n t = [t]

conKokaFields :: Ctx -> Name -> G [Type]
conKokaFields cx c
  = do ci <- conInfoOf cx c
       return (map snd (conInfoParams ci))

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

toKoka :: CT -> String -> String -> String
toKoka ct kt e
  | ctName ct == kt = e
  | otherwise
  = case ct of
      CEnum _ -> "((" ++ kt ++ ")(" ++ e ++ "))"
      CPrim _ -> "((" ++ kt ++ ")(" ++ e ++ "))"
      _ -> "kt_pun(" ++ kt ++ "," ++ e ++ ")"

fromKoka :: String -> CT -> String -> String
fromKoka kt ct e
  | ctName ct == kt = e
  | otherwise
  = case ct of
      CEnum _ -> "((" ++ ctName ct ++ ")(" ++ e ++ "))"
      CPrim p -> "((" ++ p ++ ")(" ++ e ++ "))"
      _ -> "kt_pun(" ++ ctName ct ++ "," ++ e ++ ")"

-- expressions

data Dest = DReturn | DAssign String | DDiscard

assignTo :: Dest -> CT -> String -> [String]
assignTo dest ct e
  = case dest of
      DReturn   -> ["return " ++ e ++ ";"]
      DAssign x -> [x ++ " = " ++ e ++ ";"]
      DDiscard  -> ["(void)(" ++ e ++ ");"]

indent :: [String] -> String
indent = concatMap (\l -> "  " ++ l ++ "\n")

bindVar :: Ctx -> Name -> Ty -> Ctx
bindVar cx x t = cx{ cxGamma = M.insert x t (cxGamma cx)
                  , cxValues = M.filter (S.notMember x . fvV) (M.delete x (cxValues cx))
                  , cxAliases = M.filter (/= x) (M.delete x (cxAliases cx))
                  , cxPayloads = M.filter (S.notMember x . fvV) (M.delete x (cxPayloads cx)) }

-- Pointer aliases and payload projections identify ownership slots, independently
-- of the aggregate descriptions used to omit stores.
aliasRoot :: Ctx -> Name -> Name
aliasRoot cx x = M.findWithDefault x x (cxAliases cx)

aliasCtx :: Ctx -> Maybe Name -> Name -> Ctx -> Ctx
aliasCtx source (Just z) x target
  = target{ cxAliases = M.insert x (aliasRoot source z) (cxAliases target) }
aliasCtx _ Nothing _ target = target

-- A nested alias is retained before its parent's payload is taken, then the
-- corresponding payload field is discarded. Cancel that pair: the field's
-- ownership transfers to the alias instead. DropSpec's shared path no longer
-- copies a discarded field, so the retain moves there to keep the reference
-- when the parent is shared. Search only a straight-line RC prefix up to the
-- known payload transfer, and its unique path for the discard.
cancelRetain :: Ctx -> Name -> VExpr -> G (Maybe VExpr)
cancelRetain cx retained = before
  where
    root = aliasRoot cx retained
    before expr = case expr of
      Dup x y e -> fmap (Dup x y) <$> before e
      Let x t e1@(Ret (DupV (Var _))) e -> fmap (Let x t e1) <$> before e
      Let q t (IsUnique z (UnboxRu z' p r unique) shared) e
        | z == z'
        , Just payload <- M.lookup (aliasRoot cx z) (cxPayloads cx)
        , Just unique' <- after (M.singleton p payload) unique
        -> do y <- newHiddenName <$> fresh "retain"
              return (Just (Let q t (IsUnique z (UnboxRu z' p r unique') (Dup retained y shared)) e))
      _ -> return Nothing
    after values expr = case expr of
      Unpair Owned v x y e
        | Pair a b <- replaceV values v
        -> Unpair Owned v x y <$> after (M.insert x a (M.insert y b values)) e
      Deref Owned v x e
        | Var z <- replaceV values v
        -> Deref Owned v x <$> after (M.insert x (Var (aliasRoot cx z)) values) e
      Drop x e
        | Just (Var z) <- M.lookup x values
        , aliasRoot cx z == root -> Just e
        | otherwise -> Drop x <$> after values e
      _ -> Nothing

-- Record aggregate structure, and renames at any type (such as the fields Perceus
-- re-destructures one by one): a rename keeps the bits of its source. Other scalar
-- and pointer values stay conservative: unfolding a box or closure allocation would
-- confuse equal payloads with identical pointers. Descriptions are expanded on
-- insertion so rebinding any of their free variables invalidates them directly.
valueCtx :: Ctx -> Name -> VType -> VExpr -> Ctx -> Ctx
valueCtx source x t (Ret v) target
  | aggregate t || rename v, structural v, let value = replaceV (cxValues source) v, S.notMember x (fvV value)
  = target{ cxValues = M.insert x value (cxValues target) }
  where
    rename (Var _) = True
    rename (DupV w) = rename w
    rename _ = False
    aggregate (VProd _ _) = True
    aggregate (VSum _) = True
    aggregate (VExists _ _) = True
    aggregate _ = False
    structural (Var _) = True
    structural (DupV w) = structural w
    structural (Pair a b) = structural a && structural b
    structural (Inj _ _ w) = structural w
    structural (Pack _ _ w) = structural w
    structural UnitV = True
    structural (Lit _) = True
    structural _ = False
valueCtx _ _ _ _ target = target

genE :: Ctx -> Dest -> VExpr -> G [String]
genE cx dest expr
  | Just (v,mk) <- hoistDeep expr
  = do x <- newHiddenName <$> fresh "hoist"
       let expr' = mk (Var x)
       t <- tyOf cx v
       ct <- ctype t
       s <- genE cx (DAssign (localName x)) (Ret v)
       rest <- genE (bindVar cx x (V t)) dest expr'
       return ([ctName ct ++ " " ++ localName x ++ ";"] ++ s ++ rest)
genE cx dest expr
  = case expr of
      Ret v -> do t <- tyOf cx v
                  ct <- ctype t
                  e <- genV cx v
                  return (assignTo dest ct e)
      Let x t e1 e2
        -> do ct <- ctype t
              s1 <- genE cx (DAssign (localName x)) e1
              let source = case e1 of
                             Ret _ -> cx
                             _ -> cx{ cxPayloads = M.empty }
                  cx' = (bindVar source x (V t)){ cxNamed = namedOf cx e1 x }
              s2 <- genE (valueCtx cx x t e1 cx') dest e2
              return ([ctName ct ++ " " ++ localName x ++ ";"] ++ s1 ++ s2)
      Drop x e
        | S.member x (cxShared cx)   -- like Koka's C backend: a shared block only needs a decrement
        -> do s <- genE cx dest e
              return (("kk_block_decref(kk_datatype_as_ptr(kk_datatype_unbox(" ++ localName x ++ "),_ctx),_ctx);") : s)
        | otherwise
        -> do t <- tyOfName cx x
              ct <- ctOf t
              s <- genE cx dest e
              return (filter (not . null) [dropStmt ct (localName x)] ++ s)
      Free r e
        -> do s <- genE cx dest e
              return (dropStmt CReuse (localName r) : s)
      Dup x y e
        -> do t <- tyOfName cx x
              cancelled <- cancelRetain cx x e
              let (value,body) = case cancelled of
                                   Just rest -> (localName x,rest)
                                   Nothing -> (dupExpr CBox (localName x),e)
              genAlias cx dest value (Just x) y t
                (if S.member x (cxNamed cx) then S.insert y (cxNamed cx) else cxNamed cx) body
      IsUnique x e1 e2
        -> do t <- liftC (inferVar (cxGamma cx) x)
              s1 <- genE cx dest e1
              let d = "kk_datatype_unbox(" ++ localName x ++ ")"
                  (test,shared) = case t of
                    V _ -> ("kk_datatype_is_unique(" ++ d ++ ",_ctx)", cxShared cx)   -- a lazy value may be immediate
                    A _ -> ("kk_block_is_unique(kk_datatype_as_ptr(" ++ d ++ ",_ctx))", S.insert x (cxShared cx))
              s2 <- genE cx{ cxShared = shared } dest e2
              return (["if kk_likely(" ++ test ++ ") {"]
                      ++ map ("  " ++) s1 ++ ["} else {"] ++ map ("  " ++) s2 ++ ["}"])
      UnboxRu v x r e
        -> do tv <- tyOfName cx v
              bs@[(_,V t),_] <- liftC (unboxRuBinds (cxGamma cx) v x r)
              let ve = localName v
              ct <- ctype t
              ue <- unboxV cx Borrowed (position tv /= Whole) True t ve   -- a unique box is never `box-any`
              s <- genE (foldl (\c (y,ty) -> bindVar c y ty) cx bs) dest e
              return ([ctName ct ++ " " ++ localName x ++ " = " ++ ue ++ ";",
                       "kk_reuse_t " ++ localName r ++ " = kk_datatype_as_ptr(kk_datatype_unbox(" ++ ve ++ "),_ctx);"] ++ s)
      Gen _ e -> genE cx dest e
      Join j ps e1 e2
        -> do lbl <- fresh "join"
              decls <- mapM (\(x,_,t) -> do ct <- ctype t
                                            return (ctName ct ++ " " ++ localName x ++ ";")) ps
              s2 <- genE cx{ cxJoins = M.insert j (lbl,[x | (x,_,_) <- ps]) (cxJoins cx) } dest e2
              s1 <- genE (foldl (\c (x,_,t) -> bindVar c x (V t)) cx ps) dest e1
              let (skip,end) = case dest of
                                 DReturn -> ([],[])
                                 _ -> (["goto " ++ lbl ++ "_end;"], [lbl ++ "_end: ;"])
              return (["{"] ++ map ("  " ++) (decls ++ s2 ++ skip) ++ [lbl ++ ": {"] ++ map ("  " ++) s1 ++ ["}"] ++ end ++ ["}"])
      Jump j vs
        -> do (lbl,xs) <- maybe (failG ("jump to unknown join point " ++ show j)) return (M.lookup j (cxJoins cx))
              args <- mapM (genV cx) vs
              return ([localName x ++ " = " ++ a ++ ";" | (x,a) <- zip xs args] ++ ["goto " ++ lbl ++ ";"])
      Call f tys vs -> genCall cx dest f tys vs
      App f vs
        -> do ft <- tyOfName cx f
              (ps,r) <- case ft of
                          A (AFun ps r) -> return (map snd ps, r)
                          _ -> failG ("application of " ++ show ft)
              pcts <- mapM ctype ps
              rct  <- ctype r
              let fe = localName f
              args <- mapM (genV cx) vs
              fx <- fresh "fn"
              let call = "kk_function_call(" ++ ctName rct ++ ",(kk_function_t" ++ concatMap ((", " ++) . ctName) pcts ++ ", kk_context_t*)," ++ fx ++ ",(" ++ fx ++ concatMap (", " ++) args ++ ", _ctx),_ctx)"
              return (["{ kk_function_t " ++ fx ++ " = kk_datatype_unbox(" ++ fe ++ ");"] ++ map ("  " ++) (assignTo dest rct call) ++ ["}"])
      Unpair _ v x y e
        -> do VProd a b <- tyOf cx v
              ve <- genV cx v
              z <- fresh "u"
              wct <- ctype (VProd a b)
              px <- projLeaves (VProd a b) z 0 a
              py <- projLeaves (VProd a b) z (length (leaves a)) b
              cta <- ctype a
              ctb <- ctype b
              s <- genE (contentsCtx (bindVar (bindVar cx x (V a)) y (V b)) expr (V (VProd a b)) 0 [x,y]) dest e
              return ([ctName wct ++ " " ++ z ++ " = " ++ ve ++ ";",
                       ctName cta ++ " " ++ localName x ++ " = " ++ px ++ ";",
                       ctName ctb ++ " " ++ localName y ++ " = " ++ py ++ ";"] ++ s)
      Unpack _ v tvs x e
        -> do whole@(VExists bs body) <- tyOf cx v
              let t = inst bs (map AVar tvs) body
              ve <- genV cx v
              ct <- ctype t
              s <- genE (contentsCtx (bindVar cx x (V t)) expr (V whole) 0 [x]) dest e
              return ([ctName ct ++ " " ++ localName x ++ " = " ++ ve ++ ";"] ++ s)
      Deref _ v x e
        -> do VPtr a <- tyOf cx v
              ve <- genV cx v
              genAlias cx dest ve (case v of { Var z -> Just z; _ -> Nothing }) x (A a) (case v of
                                        Var z | S.member z (cxNamed cx) -> S.insert x (cxNamed cx)
                                        _ -> cxNamed cx) e
      Unroll _ v x e
        -> do A t <- tyOfName cx v
              a <- liftC (unrollT (cxEnv cx) t)
              genAlias cx dest (localName v) (Just v) x (A a) (S.insert x (cxNamed cx)) e
      Unbox _ v x e -> genUnbox True cx dest v x e
      UnboxLazy v x e -> genUnbox False cx dest v x e
      SplitA _ v k (x,e1) (y,e2)
        -> do t <- tyOfName cx v
              [[tl@(A ls)],[tr@(A rs)]] <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
                  boundary = offset (position t) + k
              left <- genSumBranch cx dest v x tl e1
              right <- genSumBranch cx dest v y tr e2
              tg <- fresh "t"
              let (header,test) = case pointerTest ve ls rs of
                                   Just c -> ([],c)
                                   Nothing -> ([tagDecl t tg ve],tg ++ " <= " ++ show boundary)
              return (["{"] ++ map ("  " ++) (header ++ ifChain [(test,left),("true",right)]) ++ ["}"])
      CaseA _ v alts def
        -> do t <- tyOfName cx v
              tss <- liftC (altTypes (cxEnv cx) t expr)
              let ve = localName v
              brs <- forM (zip alts tss) $ \((_,x,e),ts) -> do
                [ti@(AAt p a)] <- return ts
                body <- genSumBranch cx dest v x ti e
                return ([offset p + 1 .. offset p + sumSize a],body)
              fallback <- case (def, drop (length alts) tss) of
                            (Just (x,e), [[td]]) -> Just <$> genSumBranch cx dest v x td e
                            _ -> return Nothing
              tg <- fresh "t"
              -- Match owns partitioning. Only a single runtime tag with a
              -- default needs an equality branch; nested sums cover multiple tags.
              let dispatch = case (brs,fallback) of
                    ([([tag],body)],Just other) -> ifChain [(tg ++ " == " ++ show tag,body),("true",other)]
                    _ -> switchCases tg brs fallback
              return (["{"] ++ map ("  " ++) (tagDecl t tg ve : dispatch) ++ ["}"])
      CaseV _ v alts
        -> do t@(VSum ts) <- tyOf cx v
              ve <- genV cx v
              z <- fresh "w"
              ct <- ctype t
              brs <- forM (zip3 [0..] ts alts) $ \(i,ti,(x,e)) ->
                       do cti <- ctype ti
                          s <- genE (contentsCtx (bindVar cx x (V ti)) expr (V t) i [x]) dest e
                          let bind = case ct of
                                       CEnum _ -> ctName cti ++ " " ++ localName x ++ " = kk_Unit;"
                                       CSum _ alts' ->
                                         case alts' !! i of
                                           Just _ -> ctName cti ++ " " ++ localName x ++ " = " ++ z ++ "._cons.c" ++ show i ++ ";"
                                           Nothing -> ctName cti ++ " " ++ localName x ++ " = kk_Unit;"
                                       _ -> ""
                          return ([i], bind : s)
              let tag = case ct of { CEnum _ -> z; _ -> "kk_smallint_from_integer(" ++ z ++ "._tag) - 1" }
                  dispatch = case brs of
                    [(_,body)] -> body
                    [(_,left),(_,right)] -> ifChain [("(" ++ tag ++ ") == 0",left),("true",right)]
                    _ -> switchCases tag brs (Just ["kt_unreachable();"])
              return ([ "{ " ++ ctName ct ++ " " ++ z ++ " = " ++ ve ++ ";" ] ++ dispatch ++ ["}"])
      CaseLit v alts def
        -> do tv <- tyOf cx v
              ve <- genV cx v
              brs <- forM alts $ \(l,e) ->
                       do s <- genE cx dest e
                          return (litTest ve l, s)
              sd <- genE cx dest def
              return (ifChain (brs ++ [("true", sd)]))
      CaseOpen _ v alts def
        -> do let ve = localName v
              A tv <- tyOfName cx v
              brs <- forM alts $ \(c,x,e) ->
                       do f <- liftC (openFields (cxEnv cx) c tv)
                          tys <- openTypeArgs cx v
                          (fields,kfields) <- openConFields cx c tys
                          fct <- ctype f
                          names <- conFieldNames cx c
                          fe <- openFieldExpr c fields kfields names ve
                          s <- genE (bindVar cx x (V f)) dest e
                          return ("kt_open_is(" ++ ve ++ "," ++ kokaName (makeHiddenName "tag" c) ++ ",_ctx)", (ctName fct ++ " " ++ localName x ++ " = " ++ fe ++ ";") : s)
              sd <- genE cx dest def
              return (ifChain (brs ++ [("true",sd)]))

-- bind deeply nested values first (C compilers limit the nesting of brackets)
hoistDeep :: VExpr -> Maybe (VVal, VVal -> VExpr)
hoistDeep expr
  = case expr of
      Ret v -> one v Ret
      Call f ts vs -> many vs (Call f ts)
      App f vs -> many vs (App f)
      _ -> Nothing
  where
    one v k = do (w,mk) <- deep 0 v
                 return (w,k . mk)
    many vs k = case [(i,r) | (i,v) <- zip [0..] vs, Just r <- [deep 0 v]] of
                  ((i,(w,mk)):_) -> Just (w, \x -> k (take i vs ++ [mk x] ++ drop (i+1) vs))
                  [] -> Nothing
    deep :: Int -> VVal -> Maybe (VVal, VVal -> VVal)
    -- only whole values of named types, whose tags have no offset in an enclosing sum
    deep d v
      | d >= 24 && depth v > 8, Ptr _ _ <- v = Just (v,id)
      | otherwise = case [(replace,r) | (w,replace) <- childrenV v, Just r <- [deep (d+1) w]] of
                      ((replace,(u,mk)):_) -> Just (u, replace . mk)
                      [] -> Nothing

-- nesting depth of value constructors
depth :: VVal -> Int
depth v
  = case childrenV v of
      [] -> 0
      ws -> 1 + maximum (map (depth . fst) ws)

-- Unboxed children reached through boxed constructors, with typed rebuild functions.
childrenV :: VVal -> [(VVal, VVal -> VVal)]
childrenV v = case v of
  Inj i t w -> [(w,Inj i t)]
  Pair u w -> [(u,\x -> Pair x w),(w,Pair u)]
  Ptr a w -> [(u,Ptr a . rebuild) | (u,rebuild) <- childrenA w]
  Pack t ts w -> [(w,Pack t ts)]
  TyApp w ts -> [(w,\x -> TyApp x ts)]
  DupV w -> [(w,DupV)]
  _ -> []

childrenA :: AVal -> [(VVal, VVal -> AVal)]
childrenA v = case v of
  InjA i a w -> [(u,InjA i a . rebuild) | (u,rebuild) <- childrenA w]
  Roll a w -> [(u,Roll a . rebuild) | (u,rebuild) <- childrenA w]
  Box w -> [(w,Box)]
  OpenCon c ts w -> [(w,OpenCon c ts)]
  BoxAt r w -> [(w,BoxAt r)]
  BoxIn x w -> [(w,BoxIn x)]
  _ -> []

-- A partition binder is an alias with a different static sum and tag origin.
genSumBranch :: Ctx -> Dest -> Name -> Name -> Ty -> VExpr -> G [String]
genSumBranch cx dest v x t e
  = do let named = if S.member v (cxNamed cx) then S.insert x (cxNamed cx) else cxNamed cx
           cx' = (bindVar cx x t){ cxNamed = named }
       body <- genE (aliasCtx cx (Just v) x cx') dest e
       return (["kk_box_t " ++ localName x ++ " = " ++ localName v ++ ";"] ++ body)

-- Read the tag of a boxed sum; when every alternative is a heap block, the
-- tag is in the block header and needs no pointer test.
tagDecl :: Ty -> String -> String -> String
tagDecl t tg ve = "kk_tag_t " ++ tg ++ " = " ++ tagRead ++ ";"
  where
    d = "kk_datatype_unbox(" ++ ve ++ ")"
    tagRead = case t of
                A a | shapeIsHeap a == Just True -> "kk_block_tag(kk_datatype_as_ptr(" ++ d ++ ",_ctx))"
                _ -> "kk_datatype_tag(" ++ d ++ ",_ctx)"

-- Exhaustive boxed cases also accept the dummy result of an effect yield:
-- the final arm is the default, without emitting its body twice.
switchCases :: String -> [([Int],[String])] -> Maybe [String] -> [String]
switchCases tag brs def
  = ["switch (" ++ tag ++ ") {"]
    ++ concat [branch (map (\t -> "case " ++ show t ++ ":") tags
                      ++ ["default:" | Nothing <- [def], i == length brs - 1]) body
              | (i,(tags,body)) <- zip [0..] brs]
    ++ maybe [] (branch ["default:"]) def ++ ["}"]
  where
    branch labels body = labels ++ ["{"] ++ map ("  " ++) body ++ ["  break;","}"]

ifChain :: [(String,[String])] -> [String]
ifChain [] = []
ifChain [("true",s)] = ["{"] ++ map ("  " ++) s ++ ["}"]
ifChain ((t,s):rest)
  = ["if (" ++ t ++ ") {"] ++ map ("  " ++) s ++ ["} else"] ++ ifChain' rest
  where
    ifChain' [] = ["{ kt_unreachable(); }"]
    ifChain' brs = ifChain brs

litTest :: String -> Lit -> String
litTest ve lit
  = case lit of
      LitInt i -> "kk_integer_eq_borrow(kt_unbox_integer(" ++ ve ++ ")," ++ intLit i ++ ",_ctx)"
      LitString s -> "(kk_string_cmp_cstr_borrow(kt_unbox_string(" ++ ve ++ ")," ++ fst (cstring s) ++ ",_ctx) == 0)"
      LitChar c -> "(" ++ ve ++ " == " ++ show (fromEnum c) ++ ")"
      LitFloat d -> "(" ++ ve ++ " == " ++ showHFloat d "" ++ ")"
  where
    intLit i | i >= -8191 && i <= 8191 = "kk_integer_from_small(" ++ show i ++ ")"
             | otherwise = "kk_integer_from_str(\"" ++ show i ++ "\",_ctx)"

openTypeArgs :: Ctx -> Name -> G [AType]
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

openFieldExpr :: Name -> [VType] -> [Type] -> [String] -> String -> G String
openFieldExpr c fields kfields names ve
  = do let acc n = kokaName (makeHiddenName "as" c) ++ "(kt_unbox_datatype(" ++ ve ++ "),_ctx)->" ++ n
       vals <- forM (zip3 fields kfields names) $ \(f,kt,n) ->
                 do fct <- ctype f
                    return (fromKoka (kokaCType kt) fct (acc n))
       case fields of
         [] -> return "kk_Unit"
         [_] -> return (head vals)
         _ -> do ct <- ctype (prodV fields)
                 let sname = ctName ct
                     parts = zip fields vals
                 y <- fresh "of"
                 let go i [] = []
                     go i ((f,v):rest) = let n = length (leaves f)
                                         in (if n == 1 then [y ++ ".f" ++ show i ++ " = " ++ v ++ "; "] else []) ++ go (i+n) rest
                 return ("({ " ++ sname ++ " " ++ y ++ "; " ++ concat (go 0 parts) ++ y ++ "; })")

-- calls

genCall :: Ctx -> Dest -> Name -> [AType] -> [VVal] -> G [String]
genCall cx dest f tys vs
  | f == nameLazyFree, [v] <- vs
  = do e <- genV cx v
       return (["kk_block_free(kk_datatype_as_ptr(kk_datatype_unbox(" ++ e ++ "),_ctx),_ctx);"] ++ assignTo dest CUnit "kk_Unit")
  | [Lit (LitInt i)] <- vs, Just (kt,lit) <- fixedWidthLit f i
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       return (assignTo dest rct (fromKoka kt rct lit))
  | Just (v,i,neq) <- smallIntComparison f vs
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       e <- genV cx v
       let arg = "kt_unbox_integer(" ++ e ++ ")"
           test = case i of
                    0  -> "kk_integer_is_zero_borrow(" ++ arg ++ ")"
                    1  -> "kk_integer_is_one_borrow(" ++ arg ++ ")"
                    -1 -> "kk_integer_is_minus_one_borrow(" ++ arg ++ ")"
                    _  -> "kk_integer_eq_borrow(kk_integer_from_small(" ++ show i ++ ")," ++ arg ++ ",_ctx)"
       return (assignTo dest rct (fromKoka "bool" rct (if neq then "!(" ++ test ++ ")" else test)))
  | Just (v,i) <- smallIntArithmetic f vs
  = do (_,r) <- callSig cx f tys
       rct <- ctype r
       e <- genV cx v
       let call = "kk_integer_add_small_const(kt_unbox_integer(" ++ e ++ ")," ++ show i ++ ",_ctx)"
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
                 return (["{"] ++ ["  " ++ ctName ct ++ " " ++ t ++ " = " ++ a ++ ";" | (t,a,ct) <- zip3 tmps args pcts]
                         ++ ["  " ++ localName p ++ " = " ++ t ++ ";" | (p,t) <- zip params tmps]
                         ++ ["  goto kt_tailcall;", "}"])
         _ -> return (assignTo dest rct (callName f ++ "(" ++ concatMap (++ ", ") args ++ "_ctx)"))

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
fixedWidthLit :: Name -> Integer -> Maybe (String,String)
fixedWidthLit f i
  | f `elem` [nameInt32,nameInternalInt32] && within 31 = Just ("int32_t", "KK_I32(" ++ show i ++ ")")
  | f == nameInt64 && within 63                         = Just ("int64_t", "KK_I64(" ++ show i ++ ")")
  | f `elem` [nameSSizeT,nameInternalSSizeT] && within 31 = Just ("kk_ssize_t", "KK_IZ(" ++ show i ++ ")")
  | f == nameIntPtrT && within 31                       = Just ("intptr_t", "KK_IP(" ++ show i ++ ")")
  | f == nameByte && i >= 0 && i <= 255                 = Just ("uint8_t", "((uint8_t)" ++ show i ++ ")")
  | otherwise = Nothing
  where
    within bits = abs i < 2^bits   -- excludes the minimum, which is not a valid C literal

callName :: Name -> String
callName f
  | f == newHiddenName "typed-unreachable" = "kt_unreachable_value"
  | otherwise = cName f

callSig :: Ctx -> Name -> [AType] -> G ([VType],VType)
callSig cx f tys
  = case M.lookup f (envSigs (cxEnv cx)) of
      Just (SigFun tvs ps r) -> return (map (inst tvs tys . snd) ps, inst tvs tys r)
      _ -> failG ("unknown function " ++ show f)

genExtern :: Ctx -> Dest -> Name -> [AType] -> [VVal] -> External -> G [String]
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
           call | isComment fmt = ""
                | null named    = substFormat fmt (map fst args)
                | otherwise     = "({ " ++ concat [kt ++ " " ++ n ++ " = " ++ a ++ "; " | (n,(a,kt)) <- named]  -- parameters used by name
                                  ++ substFormat fmt (map fst args) ++ "; })"
       case r of
         VUnit | null call -> return (assignTo dest CUnit "kk_Unit")
         VUnit -> return (["(void)(" ++ call ++ ");"] ++ assignTo dest CUnit "kk_Unit")
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

substFormat :: String -> [String] -> String
substFormat fmt args = go fmt
  where
    go [] = []
    go ('\\':'#':xs) = '#' : go xs
    go ('#':d:xs) | isDigit d && d /= '0' = let i = fromEnum d - fromEnum '1'
                                            in (if i < length args then "(" ++ args !! i ++ ")" else "/*missing*/") ++ go xs
    go (x:xs) = x : go xs

-- boxed values that are (parts of) values of named types, which are never Koka's `box-any`
namedOf :: Ctx -> VExpr -> Name -> S.Set Name
namedOf cx e x
  = case e of
      Ret v | Just z <- copyOf v, S.member z (cxNamed cx) -> S.insert x (cxNamed cx)
      _ -> cxNamed cx

-- a let that binds a variable or a duplicate of one binds the same value
copyOf :: VVal -> Maybe Name
copyOf v
  = case v of
      Var z -> Just z
      DupV w -> copyOf w
      _ -> Nothing

-- definitions

genDef :: Env -> CEnv -> Def -> G (String,String,String)
genDef env cenv def
  = case def of
      DefFun f _ args res body
        -> do pcts <- mapM (\(_,_,t) -> ctype t) args
              rct  <- ctype res
              let g  = M.fromList [(x,V t) | (x,_,t) <- args]
                  cx = Ctx env cenv g S.empty (Just (f,[x | (x,_,_) <- args])) M.empty M.empty M.empty M.empty S.empty
              ss <- genE cx DReturn body
              let sig = ctName rct ++ " " ++ cName f ++ "(" ++ concat [ctName ct ++ " " ++ localName x ++ ", " | ((x,_,_),ct) <- zip args pcts] ++ "kk_context_t* _ctx)"
              let label = if any ("goto kt_tailcall;" `isInfixOf`) ss then "  kt_tailcall: ;\n" else ""
              return (sig ++ ";\n", sig ++ " {\n" ++ label ++ indent ss ++ "}\n", "")
      DefVal x _ t body
        -> do ct <- ctype t
              let cx = Ctx env cenv M.empty S.empty Nothing M.empty M.empty M.empty M.empty S.empty
              ss <- genE cx DReturn body
              let initf = cName x ++ "_init"
              return ("extern " ++ ctName ct ++ " " ++ cName x ++ ";\n",
                      ctName ct ++ " " ++ cName x ++ ";\nstatic " ++ ctName ct ++ " " ++ initf ++ "(kk_context_t* _ctx) {\n" ++ indent ss ++ "}\n",
                      "  " ++ cName x ++ " = " ++ initf ++ "(_ctx);\n")

-- wrappers for top-level functions used as values
genWrapper :: Env -> CEnv -> Name -> G (String,String)
genWrapper env cenv f
  = case M.lookup f (envSigs env) of
      Just (SigFun tvs ps r)
        -> do pcts <- mapM (ctype . snd) ps
              rct  <- ctype r
              let xs  = [newHiddenName ("p" ++ show i) | i <- [0..length ps - 1]]
                  cx  = Ctx env cenv (M.fromList [(x,V t) | (x,(_,t)) <- zip xs ps]) S.empty Nothing M.empty M.empty M.empty M.empty S.empty
              body <- genCall cx DReturn f (map AVar tvs) (map Var xs)
              let sig = "static " ++ ctName rct ++ " " ++ cName f ++ "_fun(kk_function_t _fself" ++ concat [", " ++ ctName ct ++ " " ++ localName x | (x,ct) <- zip xs pcts] ++ ", kk_context_t* _ctx)"
              return (sig ++ ";\n", sig ++ " {\n  kk_function_static_drop(_fself,_ctx);\n" ++ indent body ++ "}\n")
      _ -> failG ("wrapper for unknown function " ++ show f)

-- modules

cgenModule :: CEnv -> Program -> (String,String,[String])
cgenModule cenv prog
  = let env = envOf prog
        -- (prototype, definition in the header, definition in the C file, initialization)
        genDefE :: Def -> G (Either String (String,String,String,String))
        genDefE d = do st <- get
                       case runM (genDef env cenv d) () st{ stLocal = False } of
                         Left err -> return (Left (show (defName d) ++ ": " ++ err))
                         Right ((p,c,i),st') -> do put st'
                                                   return (Right (if inHeader d st' then ("static inline " ++ p,"static inline " ++ c,"",i) else (p,"",c,i)))
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
                  modc  = cName (ceModName cenv)
                  guardN = "KT_" ++ encode (show (ceModName cenv)) ++ "_H"
                  hdr   = "#ifndef " ++ guardN ++ "\n#define " ++ guardN ++ "\n"
                          ++ concat ["#include \"" ++ h ++ "\"\n" | h <- take 1 (ceIncludes cenv)]
                          ++ runtimeHeader
                          ++ concat ["#include \"" ++ h ++ "\"\n" | h <- drop 1 (ceIncludes cenv)]
                          ++ concat [stStructs st M.! n | n <- stOrder st]
                          ++ concat [p | (p,_,_,_) <- ok]
                          ++ concat [h | (_,h,_,_) <- ok]
                          ++ "void " ++ ktInitName (ceModName cenv) ++ "(kk_context_t* _ctx);\n#endif\n"
                  csrc  = concat ["#include \"" ++ take (length h - 2) h ++ ".c\"\n" | h <- take 1 (ceIncludes cenv)]
                          ++ "#include \"" ++ "kt_" ++ encode (show (ceModName cenv)) ++ ".h\"\n"
                          ++ concat (map fst wdefs)
                          ++ concat (stDecls st)
                          ++ concat [d | (_,_,d,_) <- ok]
                          ++ concat (map snd wdefs)
                          ++ "void " ++ ktInitName (ceModName cenv) ++ "(kk_context_t* _ctx) {\n  static bool _initialized = false;\n  if (_initialized) return;\n  _initialized = true;\n"
                          ++ concat ["  " ++ i ++ "(_ctx);\n" | i <- ceImportInits cenv]
                          ++ concat [i | (_,_,_,i) <- ok]
                          ++ "}\n"
              in (hdr, csrc, errs)


-- runtime support

runtimeHeader :: String
runtimeHeader = unlines
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
  , "static inline bool kt_box_is_any(kk_box_t b, kk_context_t* _ctx) {"
  , "  return (kk_box_is_ptr(b) && kk_block_has_tag(kk_ptr_unbox(b,_ctx), KK_TAG_BOX_ANY));"
  , "}"
  , "static inline bool kt_open_is(kk_box_t b, kk_string_t tag, kk_context_t* _ctx) {"
  , "  struct kt_open_s { kk_block_t _block; kk_string_t _tag; };"
  , "  return kk_string_ptr_eq_borrow(((struct kt_open_s*)kk_datatype_as_ptr(kk_datatype_unbox(b),_ctx))->_tag, tag);"
  , "}"
  , "#endif"
  ]
