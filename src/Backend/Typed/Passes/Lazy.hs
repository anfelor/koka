-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{- Memoization of lazy values (after Perceus), as in Koka's `Backend.C.ParcReuse`.

  `memoize-target(x, size, scan)` marks `x` as the lazy value under evaluation, whose
  constructor has Koka's allocation size `size`. `memoize(x, v)` then updates `x` with `v`:
  - if `v` is a constructor that is not a singleton and whose Koka size is at most `size`,
    it is written over the block of `x`, keeping its reference count so that every
    reference sees the value;
  - otherwise `x` is freed if it is unique, and else overwritten with an indirection to `v`
    (which `lazy-eval-locked` follows).
  `lazy-eval-locked` has taken the old fields of `x` (see `Perceus`), so they are not dropped.
-}
module Backend.Typed.Passes.Lazy( lazyProgram ) where

import qualified Data.Map as M
import Common.Name
import Common.NamePrim( nameLazyMemoize, nameLazyMemoizeTarget )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Types( inst, sumTypes, varV )
import Backend.Typed.Layout( layout, blockSize )
import Backend.Typed.Names( nameLazyFree )
import Backend.Typed.Monad

type Z a = M () Int a

-- free the block of a lazy value without dropping its (taken) fields

-- lazy values under evaluation with their Koka size
type Targets = M.Map Path Int

fresh :: String -> Z Path
fresh s = state (\n -> (root (newHiddenName ("lz" ++ s ++ show n)), n+1))

lazyProgram :: Program -> (Program,[String])
lazyProgram prog
  = let tdefs = progTypes prog
        run d = case evalM (lazyE tdefs M.empty (defBody d)) () 0 of
                  Right body -> (d{ defBody = body }, [])
                  Left err   -> (d, [show (defName d) ++ ": " ++ err])
        (defs,errs) = unzip (map run (progDefs prog))
        a     = -4
        sigs = M.insert nameLazyFree (SigFun [a] [(Unique,varV a)] VUnit) (progSigs prog)
    in (prog{ progDefs = defs, progSigs = sigs }, concat errs)

lazyE :: TypeDefs -> Targets -> VExpr -> Z VExpr
lazyE tdefs targets expr
  = case expr of
      Let _ _ (Call f _ [Var x, Lit (LitInt size), _]) e | f == nameLazyMemoizeTarget
        -> lazyE tdefs (M.insert x (fromInteger size) targets) e
      Call f [t] [target,v] | f == nameLazyMemoize
        -> memoize tdefs targets t target v
      _ -> descendE pure (lazyV tdefs) (\_ e -> lazyE tdefs targets e) expr

-- lambdas have no targets
lazyV :: TypeDefs -> VVal -> Z VVal
lazyV tdefs = descendV (lazyA tdefs) (lazyV tdefs)

lazyA :: TypeDefs -> AVal -> Z AVal
lazyA tdefs val
  = case val of
      Lam ps r e -> Lam ps r <$> lazyE tdefs M.empty e
      _          -> descendA pure (lazyA tdefs) (lazyV tdefs) val

memoize :: TypeDefs -> Targets -> AType -> VVal -> VVal -> Z VExpr
memoize tdefs targets t target v
  = case (t, target) of
      (ACon tname targs, Var x) | Just tdef <- M.lookup tname tdefs, Just linfo <- tdefLazy tdef, Just body <- tdefBody tdef
        -> let shapes = sumTypes (inst (tdefParams tdef) targs body)
           in case conOf v of
                Just (i,w,rebuild) | inPlace linfo shapes (M.lookup x targets) i
                  -> return (Ret (rebuild (BoxIn x w)))
                _ -> indirect t shapes (lazyIndirect linfo) x v
      _ -> fail ("cannot memoize " ++ show target ++ " at " ++ show t)

-- Koka's decision (by its sizes); our layout must fit in every lazy constructor of that size
inPlace :: LazyInfo -> [AType] -> Maybe Int -> Int -> Bool
inPlace linfo shapes mbSize i
  = case mbSize of
      Nothing   -> False
      Just size -> let (_,newSize) = lazyCons linfo !! i
                       targets   = [ourSize s | (c,(isLazy,ksize),s) <- zip3 [0..] (lazyCons linfo) shapes
                                                , isLazy, c /= lazyIndirect linfo, ksize == size]
                   in newSize > 0 && newSize <= size && not (null targets) && ourSize (shapes !! i) <= minimum targets
  where
    ourSize (ABox p) = blockSize (layout p)
    ourSize _        = 0

-- free the lazy value if it is unique, and otherwise overwrite it with an indirection to the value
indirect :: AType -> [AType] -> Int -> Path -> VVal -> Z VExpr
indirect t shapes ind x v
  = do r <- fresh "r"
       d <- fresh "d"
       z <- fresh "z"
       a <- fresh "a"
       let ref = Ptr t (Roll t (injA shapes ind (BoxIn x (Var r))))
           shared = Dup r (Let d (VPtr t) (Ret ref) (Deref Owned (Var d) a (Drop a (Ret (Var r)))))
           unique = Let z VUnit (Call nameLazyFree [t] [Var x]) (Ret (Var r))
       return (Let r (VPtr t) (Ret v) (IsUnique x unique shared))

-- the constructor of a value of a lazy datatype: its index, payload, and how to rebuild it with another box
conOf :: VVal -> Maybe (Int, VVal, AVal -> VVal)
conOf (Ptr t (Roll t' s)) = fmap (\(i,w,re) -> (i, w, Ptr t . Roll t' . re)) (go s)
  where
    go (Box w)   = Just (0, w, id)
    go (InjA i a (Box w)) = Just (i, w, InjA i a)
    go _         = Nothing
conOf _ = Nothing

