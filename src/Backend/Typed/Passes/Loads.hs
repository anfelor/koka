-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Load the fields of products in boxes before their blocks may be released.

  Code generation reads a product in a box in place (`Layout.placeBinders`): the binder of
  `[bunbox]` is a *place*, a pointer into the block, as is the binder of `[unpack]` of a
  place, and each `[proj]` of a place reads one field where the projection is. A place is thus only valid while its block is intact, which the typing rules
  before this pass do not require: after their boxed fields are duplicated
  (`Common.dupValue`) and `z` is dropped, the contents outlive the box, and after `[unbox-ru]`
  they outlive the credit. `Linear` checks the result of this pass with places.

  An event may release the block of a box `z` if it consumes an operand that `z` is a part
  or an alias of (`owners`), or the credit `z.credit`, which is then freed or written over
  (`[unbox-ru]` itself keeps the block). Before an event, this pass projects every field of a
  place of a released block that is read after it, and the later projections reuse these
  loads. A product that is read as a whole after such an event is loaded field by field, and
  its later reads use the product of the loaded fields.
-}
module Backend.Typed.Passes.Loads( loadsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Const( Const(..) )
import Control.Monad( when )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query
import Backend.Typed.Layout( placeBinders )

-- the box of each place in scope
type Places = M.Map Path Path

-- the places read as a whole after their blocks may be released, as products of their loaded
-- fields
type Loaded = M.Map Path VVal

type L a = M (Env,Gamma,Places,Loaded) () a

loadsProgram :: Program -> (Program,[String])
loadsProgram prog = (prog{ progDefs = map fst results },concatMap snd results)
  where
    results = map run (progDefs prog)
    run d = case evalM (expr (defBody d)) (envOf prog,params d,M.empty,M.empty) () of
      Left err -> (d,[show (defName d) ++ ": " ++ err])
      Right e -> (d{ defBody = e },[])
    params (DefFun _ _ ps _ _) = M.fromList [(x,V t) | (x,_,t) <- ps]
    params DefVal{} = M.empty

expr :: VExpr -> L VExpr
expr e = do
  (env,g,ps,_) <- ask
  let (fields,whole) = mconcat [restrict rel (placeReads ps k) | (rel,k) <- continuations env ps e]
      restrict rel (fs,ws) = let inRel p = maybe False (`S.member` rel) (M.lookup p ps)
                             in (S.filter (inRel . fst) fs,S.filter inRel ws)
  products <- mapM (wholeFields g) (S.toList whole)
  let reads = S.toList (S.union fields (S.fromList [(p,ss) | (p,fs) <- products, (_,ss,_) <- fs]))
  loads <- sequence [(,,) p ss <$> fieldType g p ss | (p,ss) <- reads, M.notMember (foldl child p ss) g]
  let loaded = M.fromList [(p,foldr1 Pair [Var y | (y,_,_) <- fs]) | (p,fs) <- products]
  body <- local (\(env',g',ps',l) -> (env',g',ps',M.union loaded l))
                (bind [(y,V u) | (_,_,(y,u)) <- loads] [] (rebuild e))
  return (foldr (\(p,ss,(y,_)) b -> Proj Borrowed (Var p) ss y b) body loads)
  where
    fieldType g p ss = case M.lookup p g of
      Just (V t) | Just u <- partAt t ss -> return (foldl child p ss,u)
      _ -> fail ("projection of an unknown place: " ++ show p)
    wholeFields g p = case M.lookup p g of
      Just (V t@VProd{}) -> return (p,fieldsAt p t)
      _ -> fail ("a place that is not a product is read as a whole after its block may be released: " ++ show p)

-- Rebuild an expression with its binders in scope. A projection whose binder is already in
-- scope was loaded before an event and is reused.
rebuild :: VExpr -> L VExpr
rebuild e@(Proj _ _ _ y b) = do (_,g,_,_) <- ask
                                if M.member y g then expr b else scoped e
rebuild e = scoped e

scoped :: VExpr -> L VExpr
scoped e
  | Just ds <- destructAOf e = do
      (env,g,_,_) <- ask
      t <- liftE (inferVar g (dsScrut ds))
      ts <- liftE (altTypes env t e)
      bs <- sequence [places e xs ss >>= \ps -> bind (zip xs ss) ps (expr b) | ((xs,b),ss) <- zip (dsAlts ds) ts]
      return (dsBuild ds (dsMode ds) (dsScrut ds) bs)
  | Just ds <- destructVOf e = do
      (env,g,_,_) <- ask
      t <- liftE (inferV env g (dsScrut ds))
      ts <- liftE (altTypes env (V t) e)
      v <- value (dsScrut ds)
      bs <- sequence [places e xs ss >>= \ps -> bind (zip xs ss) ps (expr b) | ((xs,b),ss) <- zip (dsAlts ds) ts]
      return (dsBuild ds (dsMode ds) v bs)
scoped e = case e of
  Let x t a b -> Let x t <$> expr a <*> bind [(x,V t)] [] (expr b)
  LetYield x t a b c -> LetYield x t <$> expr a <*> bind [(x,V t)] [] (expr b) <*> expr c
  Join j ps a b -> Join j ps <$> bind [(x,V t) | (x,_,t) <- ps] [] (expr a) <*> expr b
  UnboxRu z r b -> do
    (_,g,_,_) <- ask
    bs <- liftE (unboxRuBinds g z r)
    UnboxRu z r <$> bind bs [] (expr b)
  IfFull r a b -> do
    (_,g,_,_) <- ask
    rt <- liftE (inferVar g r)
    case rt of
      V (VReuse _ n p) -> IfFull r <$> bind [(r,V (VReuse Full n p))] [] (expr a) <*> expr b
      _ -> fail "loads: test of a non-credit"
  _ -> descendE name value (\_ -> expr) e
  where
    name :: Path -> L Path
    name x = do (_,_,_,l) <- ask
                when (M.member x l) (fail ("a place is used as a whole operand after its block may be released: " ++ show x))
                return x

-- the places among the binders of a destructuring, with their boxes
places :: VExpr -> [Path] -> [Ty] -> L [(Path,Path)]
places e xs ts = asks (\(_,_,ps,_) -> [(x,M.findWithDefault z z ps) | (x,z) <- placeBinders (`M.member` ps) e xs ts])

bind :: [(Path,Ty)] -> [(Path,Path)] -> L a -> L a
bind bs ps = local (\(env,g,places,l) -> (env,bindAll bs g,M.union (M.fromList ps) places,l))

value :: VVal -> L VVal
value v@(Var x) = asks (\(_,_,_,l) -> M.findWithDefault v x l)
value v = descendV atom value v

-- A closure copies its captures when it is created, so its body has no places of the enclosing
-- scope, but it captures the loaded fields of a place that is read after its block may be
-- released.
atom :: AVal -> L AVal
atom (Lam ps r e) = Lam ps r <$> local (\(env,g,_,l) -> (env,bindAll [(x,V t) | (x,_,t) <- ps] g,M.empty,l)) (expr e)
atom a = descendA pure atom value a

-- The subexpressions that run after an expression may have released blocks, with the boxes
-- of those blocks. The body of a join point runs after its jumps.
continuations :: Env -> Places -> VExpr -> [(S.Set Path,VExpr)]
continuations env ps e = case e of
  Let _ _ a b -> [(releasedIn env ps a,b)]
  LetYield _ _ a b c -> [(releasedIn env ps a,b),(releasedIn env ps a,c)]
  Join _ _ a b -> [(releasedIn env ps b,a)]
  _ -> [(released env ps e,k) | k <- subExprs e]

-- the boxes of places whose blocks an expression may release, not counting its subexpressions
released :: Env -> Places -> VExpr -> S.Set Path
released env ps e
  = S.fromList [z | o <- S.toList (owners env e), (p,z) <- M.toList ps, p `within` canonical o || o == child z SCredit]

releasedIn :: Env -> Places -> VExpr -> S.Set Path
releasedIn env ps e = S.unions (released env ps e : map (releasedIn env ps) (subExprs e))

-- The operands that an expression consumes, not counting its subexpressions. A destructuring
-- of a variable only exposes its parts.
owners :: Env -> VExpr -> S.Set Path
owners env e = case e of
  Ret v -> fvV v
  Drop x _ -> S.singleton x
  Free r _ -> S.singleton r
  Jump _ vs -> S.unions (map fvV vs)
  Call f _ vs -> S.unions [fvV v | (m,v) <- zip (paramModes env f (length vs)) vs, owning m]
  App f vs -> S.insert f (S.unions (map fvV vs))
  _ | Just ds <- destructVOf e, owning (dsMode ds), not (isVar (dsScrut ds)) -> fvV (dsScrut ds)
    | otherwise -> S.empty
  where
    isVar Var{} = True
    isVar _ = False

-- The reads of places in an expression: the fields that projections read, and the places that
-- are read as a whole (a closure copies its captures when it is created).
placeReads :: Places -> VExpr -> (S.Set (Path,[Step]),S.Set Path)
placeReads ps e = case e of
  Proj _ (Var p) ss _ b | M.member p ps -> (S.singleton (p,ss),S.empty) <> placeReads ps b
  _ -> (S.empty,S.filter (`M.member` ps) operands) <> mconcat (map (placeReads ps) (subExprs e))
  where
    operands = getConst (descendB (Const . S.singleton) (Const . fvV) (\_ _ -> Const S.empty) e)

subExprs :: VExpr -> [VExpr]
subExprs e = getConst (descendB (const (Const [])) (const (Const [])) (\_ b -> Const [b]) e)
