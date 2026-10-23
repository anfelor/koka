-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
-- Licensed under the Apache License, Version 2.0.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Lower logical products to right-associated products in memory order. The
-- logical tree lives only in this pass; every emitted Pair and projection refers to
-- the normalized type. Moving fields apart is expressed by ordinary IR terms,
-- so Check and Linear validate the resulting program before C generation.
module Backend.Typed.Passes.OrderFields( orderFieldsProgram ) where

import qualified Data.Map as M
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types( Types(..), inst )
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferV, inferVar, altTypes, paramModes )
import Backend.Typed.Monad
import Backend.Typed.Product
import Backend.Typed.ValidateLayout( programTypes )

data Tree = Tree VType Form
data Form = Atom VVal | Projected VVal [Step] | Product Tree Tree | Package [AType] Tree | Empty

treeType :: Tree -> VType
treeType (Tree t _) = t

data Ctx = Ctx{ sourceEnv :: Env, sourceGamma :: Gamma, values :: M.Map Path Tree
              , typeSub :: M.Map TVar AType }
data St = St{ supply :: NameSupply, typeSupply :: Int, wraps :: [VExpr -> VExpr] }
type N a = M Ctx St a

orderFieldsProgram :: Program -> (Program,[String])
orderFieldsProgram prog
  = let run d = case runM (normalizeDef d) (Ctx (envOf prog) M.empty M.empty M.empty)
                         (St (freshFor d) firstType []) of
                  Left err -> (d,[show (defName d) ++ ": " ++ err])
                  Right (d',_) -> (d',[])
        (ds,errs) = unzip (map run (progDefs prog))
        result = prog{ progTypes = M.map normDef (progTypes prog)
                     , progSigs = M.map normSig (progSigs prog), progDefs = ds }
    in (result,concat errs)
  where
    -- Normalized existential schemas use negative names. Runtime witnesses
    -- use fresh positive names, so instantiating a named type cannot capture
    -- a witness in one of its normalized existential binders.
    firstType = maximum (0 : concatMap variablesV (programTypes prog)) + 1
    normDef d = d{ tdefBody = fmap normalizeAType (tdefBody d) }
    normSig s = case s of
      SigFun vs ps r -> SigFun vs [(m,normalizeVType t) | (m,t) <- ps] (normalizeVType r)
      SigVal vs t -> SigVal vs (normalizeVType t)
      SigCon vs ts n -> SigCon vs (map normalizeVType ts) n

fresh :: N Path
fresh = state (\st -> let (x,s) = freshPathFrom "fields" (supply st) in (x,st{ supply = s }))

freshType :: N TVar
freshType = state (\st -> (typeSupply st,st{ typeSupply = typeSupply st + 1 }))

emit :: (VExpr -> VExpr) -> N ()
emit f = modify (\st -> st{ wraps = wraps st ++ [f] })

-- Wrappers belong to the expression that evaluates their operands, never to
-- a neighbouring branch or to the body of a closure.
expression :: N VExpr -> N VExpr
expression action = do outer <- gets wraps
                       modify (\st -> st{ wraps = [] })
                       e <- action
                       ws <- gets wraps
                       modify (\st -> st{ wraps = outer })
                       return (foldr ($) e ws)

source :: VType -> N VType
source t = asks (\cx -> subst (typeSub cx) t)

nt :: VType -> N VType
nt t = normalizeVType <$> source t

na :: AType -> N AType
na a = asks (\cx -> normalizeAType (subst (typeSub cx) a))

bind :: [(Path,Ty)] -> [(Path,Tree)] -> N a -> N a
bind bs vs action = local (\cx -> cx{ sourceGamma = bindAll bs (sourceGamma cx)
                                       , values = M.union (M.fromList vs) (values cx) }) action

bindVars :: [(Path,Ty)] -> N a -> N a
bindVars bs action = do vs <- mapM value bs
                        bind bs (concat vs) action
  where
    value (x,V t) = do s <- source t; return [(x,Tree s (Atom (Var x)))]
    value (_,A _) = return []

normalizeDef :: Def -> N Def
normalizeDef d = case d of
  DefFun f vs ps r e -> do ps' <- mapM (\(x,m,t) -> (,,) x m <$> nt t) ps
                           r' <- nt r
                           e' <- bindVars [(x,V t) | (x,_,t) <- ps] (ne e)
                           return (DefFun f vs ps' r' e')
  DefVal f vs t e -> DefVal f vs <$> nt t <*> ne e

-- Destructure a normalized value, then recover its logical tree in the
-- compiler. Quantifiers are opened together, after hoisting, with fresh names.
force :: Mode -> Tree -> N Tree
force mode tree@(Tree t (Atom v)) = case t of
  VProd{} -> expand
  VExists{} -> expand
  VUnit -> return (Tree VUnit Empty)
  _ -> return tree
  where
    expand = do let (vs,fs) = productParts t
                ws <- mapM (const freshType) vs
                payload <- if null vs then return v
                           else do y <- case v of { Var x -> return (child x SPack); _ -> fresh }
                                   emit (Unpack mode v ws y)
                                   return (Var y)
                let indices = productOrder fs
                fields <- split mode payload (length fs)
                let original = [fields !! position i indices | i <- [0 .. length fs - 1]]
                return (fst3 (restore t (map AVar ws) original))
    position i xs = length (takeWhile (/= i) xs)
    fst3 (a,_,_) = a
force _ tree = return tree

-- Eliminating a logical binder must not duplicate its construction, or leave
-- a non-variable where the continuation expects a named operand.
stabilize :: Mode -> Tree -> N Tree
stabilize mode tree@(Tree t form) = case form of
  Atom Var{} -> return tree
  Atom v -> do x <- fresh
               if mode /= Borrowed then emit (Let x (normalizeVType t) (Ret v))
                 else do -- A borrowed structural value needs a borrowed root,
                         -- not a let that would acquire an owned reference.
                         -- The trivial sentinel keeps this an ordinary typed
                         -- destructuring, in normalized field order.
                         let sentinel = Lit (LitChar '\0')
                         if productOrder [t,VRaw RChar] == [0,1]
                           then emit (Proj Borrowed (Pair v sentinel) [SFst] x)
                           else emit (Proj Borrowed (Pair sentinel v) [SSnd] x)
               return (Tree t (Atom (Var x)))
  Projected v steps -> do w <- readProjected mode v steps
                          return (Tree t (Atom w))
  Product a b -> Tree t <$> (Product <$> operand a <*> operand b)
  Package ts a -> Tree t . Package ts <$> operand a
  Empty -> return tree
  where
    -- Selecting a logical tail names its construction once, but does not
    -- evaluate the physical field plans that it contains. Owned selections
    -- still materialize their operands at the ownership boundary.
    operand a@(Tree _ Projected{}) | mode == Borrowed = return a
    operand a = stabilize mode a

-- Physical paths are plans inside this pass, not eager IR destructurings.
-- Emit a path only when its selected logical field is evaluated.
split :: Mode -> VVal -> Int -> N [Form]
split _ v n = return (go [] n)
  where
    go _ 0 = []
    go ss 1 = [if null ss then Atom v else Projected v ss]
    go ss k = Projected v (ss ++ [SFst]) : go (ss ++ [SSnd]) (k-1)

readProjected :: Mode -> VVal -> [Step] -> N VVal
readProjected _ v [] = return v
readProjected mode v ss = do
  x <- case v of { Var p -> return (foldl child p ss); _ -> fresh }
  emit (Proj mode v ss x)
  return (Var x)

restore :: VType -> [AType] -> [Form] -> (Tree,[AType],[Form])
restore t ws fs = case t of
  VProd a b -> let { (x,ws1,fs1) = restore a ws fs
                  ; (y,ws2,fs2) = restore b ws1 fs1 }
               in (Tree t (Product x y),ws2,fs2)
  VExists vs b -> let { (ts,ws1) = splitAt (length vs) ws
                     ; (x,ws2,fs1) = restore (inst vs ts b) ws1 fs }
                 in (Tree t (Package ts x),ws2,fs1)
  VUnit -> (Tree t Empty,ws,fs)
  _ -> case fs of
         v:rest -> (Tree t v,ws,rest)
         [] -> error "OrderFields.restore: missing field"

gather :: Mode -> Tree -> N ([AType],[(VType,VVal)])
gather mode tree = do
  Tree t form <- force mode tree
  case form of
    Product x y -> (<>) <$> gather mode x <*> gather mode y
    Package ts x -> do (ws,fs) <- gather mode x; return (ts ++ ws,fs)
    Empty -> return ([],[])
    Atom v -> return ([],[(t,v)])
    Projected v ss -> do w <- readProjected mode v ss
                         return ([],[(t,w)])

value :: Mode -> Tree -> N VVal
value _ (Tree _ (Atom v)) = return v
value mode tree = do
  (ws,fs) <- gather mode tree
  let v = pairs [snd (fs !! i) | i <- productOrder (map fst fs)]
  return (if null ws then v else Pack (normalizeVType (treeType tree)) (map normalizeAType ws) v)

pairs :: [VVal] -> VVal
pairs [] = UnitV
pairs [v] = v
pairs (v:vs) = Pair v (pairs vs)

nv :: VVal -> N VVal
nv = nvAt Owned

nvAt :: Mode -> VVal -> N VVal
nvAt mode v = tree mode v >>= value mode

tree :: Mode -> VVal -> N Tree
tree mode v = do
  cx <- ask
  t <- liftE (inferV (sourceEnv cx) (sourceGamma cx) v) >>= source
  case v of
    Var x -> return (M.findWithDefault (Tree t (Atom v)) x (values cx))
    Pair a b -> Tree t <$> (Product <$> tree mode a <*> tree mode b)
    Pack _ ts w -> do
      sub <- asks typeSub
      Tree t . Package (map (subst sub) ts) <$> tree mode w
    UnitV -> return (Tree t Empty)
    _ -> Tree t . Atom <$> atom mode v

atom :: Mode -> VVal -> N VVal
atom mode v = case v of
  Glob f ts -> Glob f <$> mapM na ts
  Inj i t w -> Inj i <$> nt t <*> nvAt mode w
  Ptr a w -> Ptr <$> na a <*> av w
  TyApp w ts -> TyApp <$> nvAt mode w <*> mapM na ts
  DupV w -> DupV <$> nvAt Borrowed w
  Context b w -> do b' <- na b
                    w' <- local (\cx -> cx{ sourceGamma = M.insert nameHole (V (VPtr b)) (sourceGamma cx) }) (nv w)
                    return (Context b' w')
  _ -> descendV av nv v

av :: AVal -> N AVal
av a = case a of
  InjA i t w -> InjA i <$> na t <*> av w
  Roll t w -> Roll <$> na t <*> av w
  OpenCon c ts ws -> OpenCon c <$> mapM na ts <*> mapM nv ws
  Lam ps r e -> do ps' <- mapM (\(x,m,t) -> (,,) x m <$> nt t) ps
                   r' <- nt r
                   e' <- bindVars [(x,V t) | (x,_,t) <- ps] (ne e)
                   return (Lam ps' r' e')
  _ -> descendA name av nv a

name :: Path -> N Path
name x = do vs <- asks values
            case M.lookup x vs of
              Just (Tree _ (Atom (Var y))) -> return y
              Nothing -> return x
              _ -> fail ("non-variable named operand: " ++ show x)

-- Each projection stays where the source has it, so code generation reads a field where it
-- is used. The emission wrappers evaluate their operands exactly once.
ne :: VExpr -> N VExpr
ne e = expression (go e)
  where
    go expr = case expr of
      Proj mode v ss x body -> project mode v ss x body
      Unpack mode v tvs x body -> do cx <- ask
                                     t <- liftE (inferV (sourceEnv cx) (sourceGamma cx) v)
                                     tss <- liftE (altTypes (sourceEnv cx) (V t) expr)
                                     w <- tree mode v >>= force mode >>= stabilize mode
                                     case (w,tss) of
                                       (Tree _ (Package ts a),[bs]) ->
                                         local (\c -> c{ typeSub = M.union (M.fromList (zip tvs ts)) (typeSub c) })
                                           (bind (zip [x] bs) [(x,a)] (ne body))
                                       _ -> fail "unpack of a non-existential"
      Let x t a b -> do t' <- nt t; a' <- ne a; b' <- bindVars [(x,V t)] (ne b)
                        return (Let x t' a' b')
      LetYield x t a b c -> do t' <- nt t; a' <- ne a; b' <- bindVars [(x,V t)] (ne b); c' <- ne c
                               return (LetYield x t' a' b' c')
      Join j tvs ps a b -> do ps' <- mapM (\(x,m,t) -> (,,) x m <$> nt t) ps
                              a' <- bindVars [(x,V t) | (x,_,t) <- ps] (ne a)
                              Join j tvs ps' a' <$> ne b
      Jump j ts vs -> do ts' <- mapM na ts
                         descendE name nv (\_ -> ne) (Jump j ts' vs)
      Yielded t -> Yielded <$> nt t
      Call f ts vs -> do env <- asks sourceEnv
                         Call f <$> mapM na ts <*> sequence (zipWith nvAt (paramModes env f (length vs)) vs)
      CaseLit v alts def -> CaseLit <$> nvAt Borrowed v <*> mapM (\(l,b) -> (,) l <$> ne b) alts <*> ne def
      -- produced by `DropSpec` and `Reuse`, which run later
      UnboxRu{} -> fail "[unbox-ru] before Perceus"
      _ | Just ds <- destructVOf expr -> do cx <- ask
                                            t <- liftE (inferV (sourceEnv cx) (sourceGamma cx) (dsScrut ds))
                                            ts <- liftE (altTypes (sourceEnv cx) (V t) expr)
                                            v <- nvAt (dsMode ds) (dsScrut ds)
                                            es <- sequence [bindVars (zip xs bs) (ne b) | ((xs,b),bs) <- zip (dsAlts ds) ts]
                                            return (dsBuild ds (dsMode ds) v es)
        | Just ds <- destructAOf expr -> do cx <- ask
                                            t <- liftE (inferVar (sourceGamma cx) (dsScrut ds))
                                            ts <- liftE (altTypes (sourceEnv cx) t expr)
                                            z <- name (dsScrut ds)
                                            es <- sequence [bindVars (zip xs bs) (ne b) | ((xs,b),bs) <- zip (dsAlts ds) ts]
                                            return (dsBuild ds (dsMode ds) z es)
      _ -> descendE name nv (\_ -> ne) expr
    project mode v ss x body = do
      cx <- ask
      s <- liftE (inferV (sourceEnv cx) (sourceGamma cx) v)
      u <- maybe (fail "projection of a non-product") return (partAt s ss)
      selected <- tree mode v >>= select mode ss >>= stabilize mode
      bind [(x,V u)] [(x,selected)] (ne body)
    -- the logical part at the steps of a projection
    select _ [] t = return t
    select mode (s:ss) t = do
      t' <- force mode t
      case t' of
        Tree _ (Product l r) -> select mode ss (if s == SFst then l else r)
        _ -> fail "projection of a non-product"
