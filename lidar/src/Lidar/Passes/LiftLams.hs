-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Lifting of closures without captures.

  A lambda without free variables is a top-level function: each becomes a `DefFun`
  `@lam<n>-f`, with the free type variables of the lambda as its type parameters, and is used
  as the static closure `Fun g` (instantiated with those variables). `Fun` is ground, so
  `Closed` extracts the values that hold such closures.

  The lambdas are lifted bottom-up, so the body of a lifted lambda already uses the functions
  of the lambdas inside it. A lambda's parameters are owned (`[lam]`), as a closure needs
  (`[fun]`), and so is its result. A lambda that is not directly under a pointer keeps its
  form if it has free type variables, as its use needs a `[tyapp]`.
-}
module Lidar.Passes.LiftLams( liftLamsProgram ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State( State, runState, state )
import Data.List( nub )
import Lidar.Name( Name, makeHiddenName )
import Lidar.Syntax
import Lidar.Types( forallA )
import Lidar.Traversal( descendA, descendE, descendV, fvA )
import Lidar.Passes.Common( tvarsA )

liftLamsProgram :: Program -> Program
liftLamsProgram prog
  = prog{ progSigs = M.union (progSigs prog) (M.fromList [(defName d, sigOf d) | d <- lifted])
        , progDefs = concat [ds ++ [d] | (d,ds) <- results] }
  where
    results = map liftDef (progDefs prog)
    lifted = concatMap snd results
    sigOf d = SigFun (defParams d) [(m,t) | (_,m,t) <- defArgs d] (defResMode d) (defRes d)

-- a definition with its lambdas lifted, and the functions of those lambdas
liftDef :: Def -> (Def,[Def])
liftDef def
  = let (body,(_,lifted)) = runState (liftE (defBody def)) (1,[])
    in (def{ defBody = body }, reverse lifted)
  where
    -- the next number, and the functions so far (last first)
    liftE :: VExpr -> State (Int,[Def]) VExpr
    liftE = descendE pure liftV (const liftE)

    liftV val
      = do val' <- descendV liftA liftV val
           case val' of
             Ptr _ lam@(Lam ps r e) | closed lam
               -> do let tvs = nub (tvarsA S.empty lam)
                     g <- define tvs ps r e
                     return (TyApp (Ptr (forallA tvs (AFun [(m,t) | (_,m,t) <- ps] r)) (Fun g)) (map AVar tvs))
             _ -> return val'

    liftA val
      = case val of
          Lam ps r e -> do e' <- liftE e
                           let lam = Lam ps r e'
                           if closed lam && null (tvarsA S.empty lam) then Fun <$> define [] ps r e' else return lam
          _ -> descendA pure liftA liftV val

    closed lam = S.null (fvA lam)

    define :: [TVar] -> [(Path,Mode,VType)] -> VType -> VExpr -> State (Int,[Def]) Name
    define tvs ps r e
      = state (\(n,ds) -> let g = makeHiddenName ("lam" ++ show n) (defName def)
                          in (g, (n+1, DefFun g tvs ps Owned r e InlineAuto : ds)))
