-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Drop-guided reuse (after Perceus).

  A drop of a box that is a heap block becomes a drop-reuse: if the box was unique,
  its fields are dropped and its block is kept as a reuse credit (`dropReuse`). A
  `free` of a credit (from drop specialization) keeps the credit instead. A box of the same
  size that is allocated in the continuation of the drop uses that block. A credit
  that is used in some branch of a case is freed in the other branches.
  Credit descriptions follow payload destructuring and credit aliases, allowing
  code generation to specialize `box@r` by omitting unchanged field stores.
  Closures get no credits. The body of a join point (which runs at most once) asks
  its jumps for the credits it needs as extra parameters: an allocation that finds
  no credit adds one. A jump passes an available credit of each size, or an empty one.
-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Passes.Reuse( reuseProgram ) where

import qualified Data.Map as M
import Data.List( nub, (\\) )
import Data.Maybe( fromMaybe )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferV, inferVar, inferAVar, altTypes, unboxRuBinds, boxContents, reuseSize, inferE, noJoins, unrollT, trivialTy )

-- credits with the size of their block
type Credits = [(Path,Int)]

-- `reJoins`: the sizes of the credits that each join point in scope asks for
data REnv = REnv{ reEnv :: Env, reGamma :: Gamma, reJoins :: M.Map Name [Int] }

-- `rsCredits`: the available credits, newest first;
-- `rsAsked`: in the body of a join point, the credits that it asks for
data RS = RS{ rsUniq :: NameSupply, rsCredits :: Credits, rsAsked :: Maybe Credits }

type R a = M REnv RS a

fresh :: R Path
fresh = state (\s -> let (x,u) = freshPathFrom "ru" (rsUniq s) in (x,s{ rsUniq = u }))

credits :: R Credits
credits = gets rsCredits

setCredits :: Credits -> R ()
setCredits cs = modify (\s -> s{ rsCredits = cs })

asked :: R Credits
asked = gets (fromMaybe [] . rsAsked)

-- use up a credit
spend :: Path -> R ()
spend r = credits >>= setCredits . filter ((/= r) . fst)

-- a credit for a block of n bytes: an available one, or one asked for by a join point body
takeCredit :: Int -> R (Maybe Path)
takeCredit n
  = do cs <- credits
       case [r | (r,m) <- cs, m == n] of
         (r:_) -> spend r >> return (Just r)
         [] -> do mbAsked <- gets rsAsked
                  case mbAsked of
                    Just as -> do r <- fresh
                                  modify (\s -> s{ rsAsked = Just (as ++ [(r,n)]) })
                                  return (Just r)
                    Nothing -> return Nothing

-- closures start without credits; a join point body may ask for them
scope :: Maybe Credits -> R a -> R (a, Maybe Credits)
scope ask action
  = do s <- get
       put s{ rsCredits = [], rsAsked = ask }
       x <- action
       s' <- get
       put s'{ rsCredits = rsCredits s, rsAsked = rsAsked s }
       return (x, rsAsked s')

reuseProgram :: Program -> (Program,[String])
reuseProgram prog
  = let env = envOf prog
        run d = case evalM (ruE (defBody d)) (REnv env (params d) M.empty) (RS (freshFor d) [] Nothing) of
                  Right body -> (d{ defBody = body }, [])
                  Left err   -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs }, concat errs)
  where
    params d = case d of
                 DefFun{} -> M.fromList [(x,V t) | (x,_,t) <- defArgs d]
                 DefVal{} -> M.empty

bind :: [(Path,Ty)] -> R a -> R a
bind bs = local (\re -> re{ reGamma = bindAll bs (reGamma re) })

typeOfV :: VVal -> R VType
typeOfV v = do re <- ask
               liftE (inferV (reEnv re) (reGamma re) v)

typeOfName :: Path -> R Ty
typeOfName x = asks reGamma >>= liftE . (`inferVar` x)

-- expressions

ruE :: VExpr -> R VExpr
ruE expr
  | Just ds <- destructVOf expr
  = do t   <- typeOfV (dsScrut ds)
       env <- asks reEnv
       tss <- liftE (altTypes env (V t) expr)
       v   <- ruV (dsScrut ds)
       es  <- branches [(zip xs ts,e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) v es)
ruE expr
  | Just ds <- destructAOf expr
  = do t <- typeOfName (dsScrut ds)
       env <- asks reEnv
       tss <- liftE (altTypes env t expr)
       es <- branches [(zip xs ts,e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) (dsScrut ds) es)
ruE expr
  = case expr of
      Let x t e1 e2
        -> do e1' <- ruE e1
              -- Keep descriptions that are still in scope through credit aliases.
              re <- ask
              t' <- case t of
                      VReuse _ _ Nothing -> liftE (inferE (reEnv re) (reGamma re) noJoins e1')
                      _ -> return t
              Let x t' e1' <$> bind [(x,V t')] (ruE e2)
      LetYield x t e1 e2 e3
        -> do e1' <- ruE e1
              es <- branches [([(x,V t)],e2),([],e3)]
              return (LetYield x t e1' (es !! 0) (es !! 1))
      Join j ps e1 e2
        -> do (e1',as) <- scope (Just []) (bind [(x,V t) | (x,_,t) <- ps] (ruE e1))
              let rs = fromMaybe [] as
              e2' <- local (\re -> re{ reJoins = M.insert j (map snd rs) (reJoins re) }) (ruE e2)
              return (Join j (ps ++ [(r,Owned,VReuse MaybeEmpty n Nothing) | (r,n) <- rs]) e1' e2')
      Jump j vs
        -> do vs' <- mapM ruV vs
              ns  <- asks (M.findWithDefault [] j . reJoins)
              rs  <- mapM takeCredit ns
              return (Jump j (vs' ++ [maybe (NoReuse n Nothing) Var r | (r,n) <- zip rs ns]))
      CaseLit v alts def
        -> do es <- branches [([],e) | e <- map snd alts ++ [def]]
              return (CaseLit v (zip (map fst alts) es) (last es))
      Drop x e
        -> do g <- asks reGamma
              t <- liftE (inferVar g x)
              env <- asks reEnv
              case t of
                V _ -> Drop x <$> ruE e   -- a context, whose block is not reused
                A a -> dropA env a
          where
            dropA env a
              = case boxContents a >>= reuseSize of
                  Right n -> do r <- fresh
                                offer r n (dropReuse x r n) (Drop x) e
                  -- A single-constructor datatype (such as FIP padding) can hide
                  -- a reusable box. Unrolling transfers ownership without copying.
                  Left _ | Right b@(ABox s) <- unrollT env a, Right _ <- reuseSize s
                    -> do let y = child x SRoll
                          g <- asks reGamma
                          reuseParts (scopeOf (M.keys g)) . Unroll Owned x y <$> bind [(y,A b)] (ruE (Drop y e))
                  Left _ -> Drop x <$> ruE e
      Free r e
        -> do t <- typeOfName r
              case t of
                V (VReuse _ n _) -> offer r n return (Free r) e
                _ -> fail ("free of a non-credit: " ++ show r)
      IsUnique x e1 e2
        -> do es <- branches [([],e1),([],e2)]
              return (IsUnique x (es !! 0) (es !! 1))
      IfFull r e1 e2
        -> do es <- branches [([],e1),([],e2)]
              return (IfFull r (es !! 0) (es !! 1))
      UnboxRu v r e
        -> do g <- asks reGamma
              bs <- liftE (unboxRuBinds g v r)
              UnboxRu v r <$> bind bs (ruE e)
      Ret _ -> plain
      Yielded _ -> plain
      Call _ _ _ -> plain
      App _ _ -> plain
      Gen _ _ -> plain
      Dup{} -> plain
      -- destructuring forms are handled above
      Proj{} -> plain
      CaseV{} -> plain
      CaseA{} -> plain
      SplitA{} -> plain
      Deref{} -> plain
      Unroll{} -> plain
      Unbox{} -> plain
      UnboxLazy{} -> plain
      Unscalar{} -> plain
      Unpack{} -> plain
      CaseOpen{} -> plain
  where
    plain = descendE pure ruV (\_ e -> ruE e) expr

-- Make a credit available in the continuation; retain the original operation if unused.
offer :: Path -> Int -> (VExpr -> R VExpr) -> (VExpr -> VExpr) -> VExpr -> R VExpr
offer r n use unusedOp e
  = do credits >>= setCredits . ((r,n) :)
       t <- asks (M.findWithDefault (V (VReuse MaybeEmpty n Nothing)) r . reGamma)
       e' <- bind [(r,t)] (ruE e)
       unused <- any ((== r) . fst) <$> credits
       if unused then do spend r
                         return (unusedOp e')
                 else use e'

-- the paper's `[dropru]`, derived from `[if-unique]` and `[unbox-ru]`
dropReuse :: Path -> Path -> Int -> VExpr -> R VExpr
dropReuse x r n e
  = do let r' = child x SCredit
       g <- asks reGamma
       env <- asks reEnv
       s <- liftE (inferAVar g x >>= boxContents)
       let y = child x SContents
           -- the contents are read once
           readY = if M.member y g then id else Unbox Borrowed x y
       body <- dropValue (trivialTy env) fresh (scopeOf (M.keys g)) y (V s) (Ret (Var r'))
       return (readY (Let r (VReuse MaybeEmpty n Nothing) (IsUnique x (UnboxRu x r' body)
                                                  (Drop x (Ret (NoReuse n Nothing))))
                        e))

-- every branch starts with the same credits, plus those that earlier branches asked for;
-- credits used in some branch are freed in the others
branches :: [([(Path,Ty)],VExpr)] -> R [VExpr]
branches alts
  = do cs <- credits
       as0 <- asked
       rs <- sequence [do as <- asked
                          let avail = cs ++ (as \\ as0)
                          setCredits avail
                          e' <- bind bs (ruE e)
                          left <- credits
                          as' <- asked
                          return (e', [r | (r,_) <- avail ++ (as' \\ as), r `notElem` map fst left])
                      | (bs,e) <- alts]
       let usedAny = nub (concatMap snd rs)
       setCredits [c | c <- cs, fst c `notElem` usedAny]
       return [foldr Free e [r | r <- usedAny, r `notElem` used] | (e,used) <- rs]

-- values: inner boxes are allocated first

ruV :: VVal -> R VVal
ruV (Context b k) = Context b <$> bind [(nameHole,V (VPtr b))] (ruV k)
ruV v = descendV ruA ruV v

ruA :: AVal -> R AVal
ruA val
  = case val of
      Lam ps r e -> Lam ps r . fst <$> scope Nothing (bind [(x,V t) | (x,_,t) <- ps] (ruE e))
      Box w -> do tw <- typeOfV w
                  w' <- ruV w
                  case reuseSize tw of
                    Right n -> maybe (Box w') (`BoxAt` w') <$> takeCredit n
                    Left _ -> return (Box w')
      _ -> descendA pure ruA ruV val
