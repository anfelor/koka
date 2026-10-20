-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

{- Validation of `fip`, `fbip` and `tail` annotations on the final program, independently of
  the frontend's check (`Core.CheckFBIP`), whose rules it follows.

  A FIP function makes no allocations or deallocations when its owned arguments are unique.
  The check runs a definition under that assumption: `if-unique` takes its first branch,
  and a credit is full where it is bound at a full type (`[unbox-ru]`), in the first
  branch of `if-full`, and where it is the result of such a branch (through a `let` or a
  jump). On these paths:

  - `box` allocates (unless its contents need no block), as do `box@r` for a credit that may
    be empty and open constructors. A box that is not the payload of a constructor (below
    `roll`) boxes a value for polymorphism, which Koka's frontend does not count. The count
    follows the frontend: the maximum over branches, the sum in sequence, and an allocation
    in sequence with a call to the recursive group is unbounded. A call adds the
    allocations its callee is annotated with, and must be callable from the definition.
  - A drop of a value with a heap block, a `free` of a full credit and the application of an
    owned closure deallocate.
  - A `dup` shares a value and prevents its reuse, except for a borrowed function: the IR
    has no borrowed application, so applying it duplicates it first.
  - A call to the recursive group outside of a tail position uses stack. A join point runs
    in the position of its definition. As in the frontend, a call whose continuation only
    destructures values and builds the result from them is in a tail position (modulo
    product contexts).

  As in the frontend, `int` is assumed small (it is neither shared nor freed), and literals,
  scalars and globals are not counted. The frontend checks a function before its monadic
  translation, so the paths on which an effect yields (`yielding()`) are not taken either,
  and the evidence operations (`evv-*`) that open effects are free. Neither are paths that
  end in a pattern match failure. The frontend does not report on
  `std/core/debug`, and neither does this check.
-}
module Backend.Typed.Fip( checkFip ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List( nub, intercalate, isPrefixOf )
import Data.Functor.Const( Const(..) )
import Control.Monad( unless, when )
import Common.Name
import Common.NamePrim( nameTpInt, nameYielding, nameCoreDebug, nameCoreHnd, namePatternMatchError )
import Common.Syntax( Fip(..), FipAlloc(..), fipAlloc, isFipTop )
import Backend.Typed.Syntax
import Backend.Typed.Common
import Backend.Typed.Monad
import Backend.Typed.Names( nameUnreachable, nameLazyFree )
import Backend.Typed.Layout( layout, isBlock )
import Backend.Typed.Pretty( ppr )
import Backend.Typed.Query( Env, Gamma, envOf, bindAll, inferVar, inferV, altTypes, unboxRuBinds, trivialTy )

-- The allocations of the most allocating path; whether there are allocations, calls to the
-- recursive group, and both in sequence; and the types of the values boxed for polymorphism.
data Cost = Cost{ cAlloc :: FipAlloc, cAllocs :: Bool, cSelf :: Bool, cLoop :: Bool, cBoxed :: S.Set String }

-- sequential composition
instance Semigroup Cost where
  Cost n a s l b <> Cost n' a' s' l' b'
    = Cost (n <> n') (a || a') (s || s') (l || l' || (a && s') || (a' && s)) (S.union b b')

instance Monoid Cost where
  mempty = Cost (AllocAtMost 0) False False False S.empty

-- alternative composition
alternatives :: [Cost] -> Cost
alternatives = foldr alt mempty
  where
    alt (Cost n a s l b) (Cost n' a' s' l' b') = Cost (max n n') (a || a') (s || s') (l || l') (S.union b b')

allocation :: Cost
allocation = mempty{ cAlloc = AllocAtMost 1, cAllocs = True }

-- the definition under check: its annotation, its recursive group, the annotations of all
-- functions, and its borrowed parameters
data Info = Info{ iFip :: Fip, iGroup :: S.Set Name, iFips :: M.Map Name Fip, iBorrowed :: [Path] }

-- a join point in scope: its instance, parameters, body, and the environment of its definition
data JoinPt = JoinPt Int [(Path,Mode,VType)] VExpr FEnv

-- `fFull`: the credits that are full besides those of a full type;
-- `fYielding`: the results of `yielding()`; `fFailing`: the join points whose bodies fail
data FEnv = FEnv{ fInfo :: Info, fEnv :: Env, fGamma :: Gamma, fFull :: S.Set Path, fYielding :: S.Set Path
                , fJoins :: M.Map Name JoinPt, fFailing :: S.Set Name, fTail :: Bool }

-- `fsRuns`: the results of the join point bodies, for each instance and the fullness of its arguments
data FS = FS{ fsUniq :: Int, fsRuns :: M.Map (Int,[Bool]) (Cost,Bool), fsMsgs :: [String] }

type F a = M FEnv FS a

-- the messages for the definitions with a `fip`, `fbip` or `tail` annotation; `groups` gives
-- the recursive group of each definition
checkFip :: M.Map Name Fip -> M.Map Name (S.Set Name) -> Program -> [String]
checkFip fips groups prog
  = concat [checkDef d fip | d@DefFun{} <- progDefs prog, qualifier (defName d) /= nameCoreDebug
                            , Just fip <- [M.lookup (defName d) fips], not (isFipTop fip)]
  where
    checkDef d fip
      = let info = Info fip (M.findWithDefault S.empty (defName d) groups) fips [x | (x,Borrowed,_) <- defArgs d]
            fenv = FEnv info (envOf prog) (M.fromList [(x,V t) | (x,_,t) <- defArgs d]) S.empty S.empty M.empty S.empty True
            label msg = show (defName d) ++ ": " ++ show fip ++ " fun: " ++ msg
        in case runM (fipE (defBody d)) fenv (FS 0 M.empty []) of
             Right ((cost,_),st) -> map label (nub (fsMsgs st) ++ allocMsg fip cost)
             Left err -> [label ("internal: " ++ err)]

allocMsg :: Fip -> Cost -> [String]
allocMsg fip cost
  = ["function allocates " ++ prettyAlloc n ++ " but was declared as allocating " ++ prettyAlloc (fipAlloc fip) ++ boxed
    | n > fipAlloc fip]
  where
    n = if cLoop cost then AllocUnlimited else cAlloc cost
    boxed | S.null (cBoxed cost) = ""
          | otherwise = " (it boxes values for polymorphism as " ++ intercalate ", " (S.toList (cBoxed cost)) ++ ")"

prettyAlloc :: FipAlloc -> String
prettyAlloc a
  = case a of
      AllocAtMost 0  -> "nothing"
      AllocAtMost n  -> "at most " ++ show n
      AllocFinitely  -> "a finite amount"
      AllocUnlimited -> "unlimited"

mayAlloc, mayDealloc, mayRecurse :: Fip -> Bool
mayAlloc fip = fipAlloc fip == AllocUnlimited
mayDealloc fip
  = case fip of
      Fip _ -> False
      _     -> True
mayRecurse fip
  = case fip of
      Fip _    -> False
      Fbip _ t -> not t
      NoFip t  -> not t

-- `callable f g`: a function annotated with f may be called from one annotated with g
callable :: Fip -> Fip -> Bool
callable f g
  = case (f,g) of
      (Fip _, _)        -> True
      (Fbip _ _, Fbip _ _) -> True
      (_, NoFip _)      -> True
      _                 -> False

warn :: String -> F ()
warn msg = modify (\s -> s{ fsMsgs = fsMsgs s ++ [msg] })

-- report the message unless the annotation allows it
require :: (Fip -> Bool) -> String -> F ()
require may msg
  = do fip <- asks (iFip . fInfo)
       unless (may fip) (warn msg)

bind :: [(Path,Ty)] -> F a -> F a
bind bs = local (\fe -> fe{ fGamma = bindAll bs (fGamma fe) })

withFull :: [Path] -> F a -> F a
withFull rs = local (\fe -> fe{ fFull = S.union (S.fromList rs) (fFull fe) })

nonTail :: F a -> F a
nonTail = local (\fe -> fe{ fTail = False })

typeOfVar :: Path -> F Ty
typeOfVar x = asks fGamma >>= liftE . flip inferVar x

isFull :: Path -> F Bool
isFull r
  = do full <- asks fFull
       t <- typeOfVar r
       return (S.member r full || isFullType t)
  where
    isFullType (V (VReuse Full _ _)) = True
    isFullType _ = False

-- whether a value is a full credit
fullV :: VVal -> F Bool
fullV v
  = case v of
      Var r -> isFull r
      _     -> return False

-- values that need no reference counting, and `int`, which the frontend assumes to be small
untracked :: Ty -> F Bool
untracked t
  = do env <- asks fEnv
       return (trivialTy env t || isInt t)
  where
    isInt (A a) = isIntA a
    isInt (V (VPtr a)) = isIntA a
    isInt _ = False
    isIntA (ACon n []) = n == nameTpInt
    isIntA _ = False

-- `x` is an immediate value on this path: one of its binders that keeps its pointer has no block
immediate :: Path -> F Bool
immediate x
  = do g <- asks fGamma
       return (or [noBlock a | (y,A a) <- M.toList g, y `within` x, all keepsPtr (stepsFrom x y)])
  where
    keepsPtr s = case s of
                   SDeref  -> True
                   SRoll   -> True
                   SInjA _ -> True
                   SRest   -> True
                   SLo     -> True
                   SHi     -> True
                   SPack   -> True
                   _       -> False
    noBlock a = case a of
                  AUnit   -> True
                  ASum ts -> all ((== AUnit) . snd) ts
                  _       -> False

isBorrowed :: Path -> F Bool
isBorrowed x = asks (any (x `within`) . iBorrowed . fInfo)

-- the cost of an expression, and whether the credit it returns (if any) is full
fipE :: VExpr -> F (Cost,Bool)
fipE expr
  | Just ds <- destructAOf expr
  = do t <- typeOfVar (dsScrut ds)
       destruct t ds id
  | Just ds <- destructVOf expr
  = do fe <- ask
       t <- liftE (inferV (fEnv fe) (fGamma fe) (dsScrut ds))
       c <- fipV (dsScrut ds)
       -- the first alternative of a test of `yielding()` is `false`
       let taken = case dsScrut ds of
                     Var x | S.member x (fYielding fe) -> take 1
                     _ -> id
       (c',full) <- destruct (V t) ds taken
       return (c <> c',full)
  where
    destruct t ds taken
      = do env <- asks fEnv
           tss <- liftE (altTypes env t expr)
           alive <- alivePaths
           branches (taken [bind (zip xs ts) (fipE e) | ((xs,e),ts) <- zip (dsAlts ds) tss, alive e])
fipE expr
  = case expr of
      Ret v -> (,) <$> fipV v <*> fullV v
      Let x t (Call f _ []) e2 | f == nameYielding
        -> local (\fe -> fe{ fYielding = S.insert x (fYielding fe) }) (bind [(x,V t)] (fipE e2))
      Let x t e1 e2
        -> do tl <- asks fTail
              let tailModProduct = tl && modProduct S.empty e2
              (c1,full) <- (if tailModProduct then id else nonTail) (fipE e1)
              (c2,full') <- bind [(x,V t)] (withFull [x | full] (fipE e2))
              return (c1 <> c2,full')
      Call f _ vs
        -> do cs <- mapM fipV vs
              c <- call f
              return (mconcat cs <> c,False)
      App f vs
        -> do cs <- mapM fipV vs
              b <- isBorrowed f
              unless b (require mayDealloc ("owned calls to functions require deallocation: " ++ show f))
              return (mconcat cs,False)
      CaseLit v alts def
        -> do c <- fipV v
              alive <- alivePaths
              (c',full) <- branches [fipE e | e <- map snd alts ++ [def], alive e]
              return (c <> c',full)
      Gen _ e -> fipE e
      Drop x e
        -> do t <- typeOfVar x
              u <- untracked t
              i <- immediate x
              unless (u || i) (require mayDealloc ("dropping " ++ show x ++ " causes deallocation"))
              fipE e
      Free r e
        -> do full <- isFull r
              when full (require mayDealloc ("freeing the reuse credit " ++ show r ++ " causes deallocation"))
              fipE e
      Dup x e
        -> do t <- typeOfVar x
              u <- untracked t
              b <- isBorrowed x
              unless (u || (b && isFun t))
                (require mayAlloc ("the variable " ++ show x ++ " is duplicated (causing sharing and preventing reuse)"))
              fipE e
      IsUnique _ e1 _ -> fipE e1
      IfFull r e1 e2
        -> do full <- isFull r
              alive <- alivePaths
              if full then fipE e1 else branches ([withFull [r] (fipE e1) | alive e1] ++ [fipE e2 | alive e2])
      UnboxRu z r e
        -> do g <- asks fGamma
              bs <- liftE (unboxRuBinds g z r)
              bind bs (fipE e)
      Join j ps e1 e2
        -> do i <- state (\s -> (fsUniq s, s{ fsUniq = fsUniq s + 1 }))
              failing <- asks fFailing
              let enter fe = fe{ fJoins = M.insert j (JoinPt i ps e1 fe) (fJoins fe)
                               , fFailing = if fails failing e1 then S.insert j failing else failing }
              local enter (fipE e2)
      Jump j vs
        -> do cs <- mapM fipV vs
              (c,full) <- jump j vs
              return (mconcat cs <> c,full)
      _ -> fail ("unexpected expression: " ++ ppr expr)
  where
    isFun t = case t of
                V (VPtr a) -> isFunA a
                A a        -> isFunA a
                _          -> False
    isFunA a = case a of
                 AFun _ _      -> True
                 AForall _ b   -> isFunA b
                 _             -> False

-- the expressions that do not fail
alivePaths :: F (VExpr -> Bool)
alivePaths = asks (\fe -> not . fails (fFailing fe))

-- every path of an expression ends in a pattern match failure (or is unreachable), given the
-- join points whose bodies fail
fails :: S.Set Name -> VExpr -> Bool
fails failing expr
  = case expr of
      Call f _ _ -> f == namePatternMatchError || f == nameUnreachable
      Jump j _ -> S.member j failing
      Let _ _ e1 e2 -> fails failing e1 || fails failing e2
      Join j _ e1 e2 -> fails (if fails failing e1 then S.insert j failing else failing) e2
      _ -> let es = subexprs expr in not (null es) && all (fails failing) es

-- the continuation of a call only destructures values and builds its result from values, given
-- the join points (in the continuation) whose bodies do so as well
modProduct :: S.Set Name -> VExpr -> Bool
modProduct joins expr
  = case expr of
      Ret _ -> True
      Call f _ _ -> isEvidence f
      App _ _ -> False
      CaseLit{} -> False
      Jump j _ -> S.member j joins
      Let x _ (Call f _ []) e2 | f == nameYielding
        -> case e2 of
             CaseV _ (Var y) ((_,e):_) | y == x -> modProduct joins e
             _ -> modProduct joins e2
      Let _ _ e1 e2 -> modProduct S.empty e1 && modProduct joins e2
      Join j _ e1 e2 -> modProduct (if modProduct joins e1 then S.insert j joins else joins) e2
      _ | Just ds <- destructAOf expr -> single (dsAlts ds)
        | Just ds <- destructVOf expr -> single (dsAlts ds)
        | otherwise -> all (modProduct joins) (subexprs expr)
  where
    single [(_,e)] = modProduct joins e
    single _ = False

-- the subexpressions of an expression
subexprs :: VExpr -> [VExpr]
subexprs = getConst . descendE (const (Const [])) (const (Const [])) (\_ e -> Const [e])

-- an operation on the evidence vector that opens an effect
isEvidence :: Name -> Bool
isEvidence f = qualifier f == nameCoreHnd && "evv-" `isPrefixOf` nameLocal f

branches :: [F (Cost,Bool)] -> F (Cost,Bool)
branches fs
  = do rs <- sequence fs
       return (alternatives (map fst rs),all snd rs)

-- the body of a join point for the arguments of a jump, once for each fullness of the arguments
jump :: Name -> [VVal] -> F (Cost,Bool)
jump j vs
  = do js <- asks fJoins
       JoinPt i ps body fe <- maybe (fail ("unknown join point " ++ show j)) return (M.lookup j js)
       fulls <- mapM fullV vs
       runs <- gets fsRuns
       case M.lookup (i,fulls) runs of
         Just r -> return r
         Nothing -> do let enter = fe{ fGamma = bindAll [(x,V t) | (x,_,t) <- ps] (fGamma fe)
                                     , fFull = S.union (S.fromList [x | ((x,_,_),True) <- zip ps fulls]) (fFull fe) }
                       r <- local (const enter) (fipE body)
                       modify (\s -> s{ fsRuns = M.insert (i,fulls) r (fsRuns s) })
                       return r

call :: Name -> F Cost
call f
  = do info <- asks fInfo
       tl <- asks fTail
       let self = S.member f (iGroup info)
       when (self && not tl) (require mayRecurse ("non-tail call to a (mutually) recursive function: " ++ show f))
       if f == nameUnreachable || f == nameYielding || isEvidence f then return mempty
       else if f == nameLazyFree then do require mayDealloc "freeing a lazy value causes deallocation"
                                         return mempty
       else case M.lookup f (iFips info) of
              Nothing -> do warn ("no fip information for the function " ++ show f)
                            return mempty
              Just fip | callable fip (iFip info) -> return (credits fip){ cSelf = self }
                       | otherwise -> do warn ("calling a non-fip function: " ++ show f)
                                         return mempty
  where
    credits fip = case fip of
                    Fip n    -> mempty{ cAlloc = n }
                    Fbip n _ -> mempty{ cAlloc = n }
                    NoFip _  -> mempty

fipV :: VVal -> F Cost
fipV v
  = case v of
      Ptr t a -> fipA (Just t) a
      Context b k -> bind [(nameHole,V (VPtr b))] (fipV k)
      _ -> mconcat <$> sequence (getConst (descendV (\a -> Const [fipA Nothing a]) (\w -> Const [fipV w]) v))

-- the cost of a boxed value, given the type of the pointer to it unless it is the payload of a
-- constructor
fipA :: Maybe AType -> AVal -> F Cost
fipA ptr val
  = case val of
      Box w -> do c <- fipV w
                  b <- boxing w
                  return (c <> b)
      BoxAt r w -> do c <- fipV w
                      full <- isFull r
                      b <- boxing w
                      return (if full then c else c <> b)
      Roll _ a -> fipA Nothing a
      InjA _ _ a -> fipA ptr a
      OpenCon _ _ w -> (<> allocation) <$> fipV w
      Lam ps _ e -> do require mayAlloc "allocating a lambda expression"
                       let enter fe = fe{ fGamma = bindAll [(x,V t) | (x,_,t) <- ps] (fGamma fe), fJoins = M.empty, fTail = False }
                       fst <$> local enter (fipE e)
      _ -> mconcat <$> sequence (getConst (descendA (const (Const [])) (\a -> Const [fipA Nothing a]) (\w -> Const [fipV w]) val))
  where
    boxing w
      = do fe <- ask
           t <- liftE (inferV (fEnv fe) (fGamma fe) w)
           return (if not (isBlock (layout t)) then mempty
                   else maybe allocation (\a -> allocation{ cBoxed = S.singleton (ppr (A a)) }) ptr)
