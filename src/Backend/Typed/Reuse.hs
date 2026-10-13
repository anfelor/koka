-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Drop-guided reuse (after Perceus).

  A drop of a box that is a heap block becomes a drop-reuse: if the box was unique,
  its fields are dropped and its block is kept as a reuse credit. A box of the same
  size that is allocated in the continuation of the drop uses that block. A credit
  that is used in some branch of a case is dropped (freed) in the other branches.
  Closures get no credits. The body of a join point (which runs at most once) asks
  its jumps for the credits it needs as extra parameters: an allocation that finds
  no credit adds one. A jump passes an available credit of each size, or an empty one.
-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Backend.Typed.Reuse( reuseProgram ) where

import qualified Data.Map as M
import Data.List( nub, (\\) )
import Data.Maybe( fromMaybe )
import Common.Name
import Backend.Typed.Syntax
import Backend.Typed.Monad
import Backend.Typed.Check( Env, Gamma, envOf, bindAll, inferV, altTypes, boxContents, reuseSize )

-- credits with the size of their block
type Credits = [(Name,Int)]

-- `reJoins`: the sizes of the credits that each join point in scope asks for
data REnv = REnv{ reEnv :: Env, reGamma :: Gamma, reJoins :: M.Map Name [Int] }

-- `rsCredits`: the available credits, newest first;
-- `rsAsked`: in the body of a join point, the credits that it asks for
data RS = RS{ rsUniq :: Int, rsCredits :: Credits, rsAsked :: Maybe Credits }

type R a = M REnv RS a

fresh :: R Name
fresh = state (\s -> (newHiddenName ("ru" ++ show (rsUniq s)), s{ rsUniq = rsUniq s + 1 }))

credits :: R Credits
credits = gets rsCredits

setCredits :: Credits -> R ()
setCredits cs = modify (\s -> s{ rsCredits = cs })

asked :: R [Name]
asked = gets (maybe [] (map fst) . rsAsked)

-- use up a credit
spend :: Name -> R ()
spend r = credits >>= setCredits . filter ((/= r) . fst)

-- a credit for a block of n bytes: an available one, or one asked for by a join point body
takeCredit :: Int -> R (Maybe Name)
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
        run d = case evalM (ruE (defBody d)) (REnv env (params d) M.empty) (RS 0 [] Nothing) of
                  Right body -> (d{ defBody = body }, [])
                  Left err   -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
    in (prog{ progDefs = defs }, concat errs)
  where
    params d = case d of
                 DefFun{} -> M.fromList [(x,V t) | (x,_,t) <- defArgs d]
                 DefVal{} -> M.empty

bind :: [(Name,Ty)] -> R a -> R a
bind bs = local (\re -> re{ reGamma = bindAll bs (reGamma re) })

typeOfV :: Val -> R Ty
typeOfV v = do re <- ask
               liftE (inferV (reEnv re) (reGamma re) v)

-- expressions

ruE :: Expr -> R Expr
ruE expr
  | Just ds <- destructOf expr
  = do t   <- typeOfV (dsScrut ds)
       env <- asks reEnv
       tss <- liftE (altTypes env t expr)
       v   <- ruV (dsScrut ds)
       es  <- branches [(zip xs ts,e) | ((xs,e),ts) <- zip (dsAlts ds) tss]
       return (dsBuild ds (dsMode ds) v es)
ruE expr
  = case expr of
      Let x t e1 e2 -> Let x t <$> ruE e1 <*> bind [(x,t)] (ruE e2)
      Join j ps e1 e2
        -> do (e1',as) <- scope (Just []) (bind [(x,V t) | (x,_,t) <- ps] (ruE e1))
              let rs = fromMaybe [] as
              e2' <- local (\re -> re{ reJoins = M.insert j (map snd rs) (reJoins re) }) (ruE e2)
              return (Join j (ps ++ [(r,Owned,VReuse n) | (r,n) <- rs]) e1' e2')
      Jump j vs
        -> do vs' <- mapM ruV vs
              ns  <- asks (M.findWithDefault [] j . reJoins)
              rs  <- mapM takeCredit ns
              return (Jump j (vs' ++ [maybe (NoReuse n) Var r | (r,n) <- zip rs ns]))
      CaseLit v alts def
        -> do es <- branches [([],e) | e <- map snd alts ++ [def]]
              return (CaseLit v (zip (map fst alts) es) (last es))
      Drop x e
        -> do tx <- typeOfV (Var x)
              case boxContents tx >>= reuseSize of
                Left _  -> Drop x <$> ruE e
                Right n -> do r <- fresh
                              credits >>= setCredits . ((r,n) :)
                              e' <- bind [(r,V (VReuse n))] (ruE e)
                              unused <- any ((== r) . fst) <$> credits
                              if unused then do spend r
                                                return (Drop x e')
                                        else return (DropRu x r e')
      Ret _ -> plain
      Call _ _ _ -> plain
      App _ _ -> plain
      Gen _ _ -> plain
      -- destructuring forms are handled above
      Unpair{} -> plain
      CaseV{} -> plain
      CaseA{} -> plain
      Unfold{} -> plain
      Unbox{} -> plain
      UnboxLazy{} -> plain
      Unpack{} -> plain
      CaseOpen{} -> plain
      -- only produced by reuse and drop specialization
      DropRu{} -> fail "drop-reuse before reuse"
      IsUnique{} -> fail "uniqueness test before reuse"
      UnboxRu{} -> fail "unbox-reuse before reuse"
  where
    plain = descendE ruV (\_ e -> ruE e) expr

-- every branch starts with the same credits; credits used in some branch are dropped in the others
branches :: [([(Name,Ty)],Expr)] -> R [Expr]
branches alts
  = do cs <- credits
       rs <- mapM (\(bs,e) -> do setCredits cs
                                 as <- asked
                                 e' <- bind bs (ruE e)
                                 left <- credits
                                 as' <- asked
                                 return (e', [r | (r,_) <- cs, r `notElem` map fst left] ++ (as' \\ as))) alts
       let usedAny = nub (concatMap snd rs)
       setCredits [c | c <- cs, fst c `notElem` usedAny]
       return [foldr Drop e [r | r <- usedAny, r `notElem` used] | (e,used) <- rs]

-- values: inner boxes are allocated first

ruV :: Val -> R Val
ruV val
  = case val of
      Lam ps r e -> Lam ps r . fst <$> scope Nothing (bind [(x,V t) | (x,_,t) <- ps] (ruE e))
      Box w -> do tw <- typeOfV w
                  w' <- ruV w
                  case tw of
                    V t | Right n <- reuseSize t
                      -> maybe (Box w') (`BoxAt` w') <$> takeCredit n
                    _ -> return (Box w')
      _ -> descendV ruV val
