-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.ElabType( Tr
                             , elabType, elabFunType, elabScheme
                             , isValueInfo, elabArgs
                             , conIndex, conFieldTypes, schemeFieldTypes, conCount, conShape, conExists
                             , typeDefs, dataInfoOf, valueBody
                             , tvarStar
                             ) where

import qualified Data.Map as M
import Data.List( elemIndex )
import Common.Name
import Common.NamePrim
import Common.Syntax( dataDefIsValue, dataDefIsOpen, Platform )
import Core.Core( conReprAllocSize, getConRepr )
import Kind.Kind( Kind, hasKindStarResult, isKindStar, extractKindFun )
import Kind.Newtypes
import Type.Type
import qualified Common.NameMap as NM
import Backend.Typed.Syntax
import Backend.Typed.Types

type Tr a = Either String a

tvarStar :: TypeVar -> Bool
tvarStar tv = hasKindStarResult (typevarKind tv)

tvarId :: TypeVar -> TVar
tvarId = typevarId

elabType :: Newtypes -> Type -> Tr VType
elabType nt tp
  = case tp of
      TSyn _ _ t     -> elabType nt t
      TVar tv | tvarStar tv -> Right (VVar (tvarId tv))
      TFun _ _ _     -> VPtr <$> elabFunType nt tp
      TForall tvs rho | not (any tvarStar tvs) -> elabType nt rho
      TForall tvs rho -> do t <- elabType nt rho
                            case t of
                              _ | not (any (`elem` map tvarId tvs) (ftv t)) -> Right t
                              VPtr a -> Right (VPtr (forallA (map tvarId (filter tvarStar tvs)) a))
                              _ -> Left ("quantification over a non-pointer type: " ++ show t)
      TCon tc        -> elabCon nt (typeconName tc) []
      TApp (TCon tc) args -> elabCon nt (typeconName tc) args
      TApp (TSyn _ _ t) args -> elabType nt (TApp t args)
      TApp (TVar tv) args | tvarStar tv -> VApp (tvarId tv) <$> elabArgsK nt (fst (extractKindFun (typevarKind tv))) args
      _              -> Left ("unsupported type: " ++ show tp)

elabFunType :: Newtypes -> Type -> Tr AType
elabFunType nt tp
  = case tp of
      TSyn _ _ t      -> elabFunType nt t
      TForall tvs rho -> forallA (map tvarId (filter tvarStar tvs)) <$> elabFunType nt rho
      TFun pars _ res -> AFun <$> mapM (\(_,t) -> (,) Owned <$> elabType nt t) pars <*> elabType nt res
      _ -> do t <- elabType nt tp
              case t of
                VPtr a -> Right a
                _      -> Left ("quantification over a non-pointer type: " ++ show t)

elabScheme :: Newtypes -> Type -> Tr ([TVar],VType)
elabScheme nt tp
  = case tp of
      TSyn _ _ t      -> elabScheme nt t
      TForall tvs rho -> (,) (map tvarId (filter tvarStar tvs)) <$> elabType nt rho
      _               -> (,) [] <$> elabType nt tp

dataInfoOf :: Newtypes -> Name -> Tr DataInfo
dataInfoOf nt name
  = maybe (Left ("unknown datatype: " ++ show name)) Right (newtypesLookupAny name nt)

elabCon :: Newtypes -> Name -> [Type] -> Tr VType
elabCon nt name args
  = do info  <- dataInfoOf nt name
       vargs <- elabArgs nt (dataInfoParams info) args
       let ids = map tvarId (filter tvarStar (dataInfoParams info))
           rest = drop (length vargs) ids
       if not (isValueInfo info) then Right (VCon name vargs)
       else if null rest then valueBody nt info vargs
       else VTLam rest <$> valueBody nt info (vargs ++ map VVar rest)

elabArgs :: Newtypes -> [TypeVar] -> [Type] -> Tr [VType]
elabArgs nt tvs args = elabArgsK nt (map typevarKind tvs) args

elabArgsK :: Newtypes -> [Kind] -> [Type] -> Tr [VType]
elabArgsK nt kinds args = sequence [elabArg nt k arg | (k,arg) <- zip kinds args, hasKindStarResult k]

elabArg :: Newtypes -> Kind -> Type -> Tr VType
elabArg nt k arg
  | isKindStar k = boxrep <$> elabType nt arg
  | otherwise    = elabType nt arg

isValueInfo :: DataInfo -> Bool
isValueInfo info = dataDefIsValue (dataInfoDef info) || dataInfoName info == nameTpUnit

valueBody :: Newtypes -> DataInfo -> [VType] -> Tr VType
valueBody nt info vargs
  = case dataInfoConstrs info of
      []    -> Right (VRaw (dataInfoName info))
      [con] -> conValueFields nt vargs con
      cons  -> VSum <$> mapM (conValueFields nt vargs) cons

conValueFields :: Newtypes -> [VType] -> ConInfo -> Tr VType
conValueFields nt vargs con = existsV (conExists con) <$> conFields nt vargs con

existsV :: [TVar] -> VType -> VType
existsV [] t  = t
existsV tvs t = VExists tvs t

conFields :: Newtypes -> [VType] -> ConInfo -> Tr VType
conFields nt vargs con = prodV <$> conFieldTypes nt vargs con

conFieldTypes :: Newtypes -> [VType] -> ConInfo -> Tr [VType]
conFieldTypes nt vargs con = schemeFieldTypes nt vargs (conInfoType con)

schemeFieldTypes :: Newtypes -> [VType] -> Type -> Tr [VType]
schemeFieldTypes nt vargs scheme
  = do let (_,fields,params,_) = conScheme scheme
           sub = M.fromList (zip (map tvarId params) vargs)
       map (subst sub) <$> mapM (elabType nt) fields

conScheme :: Type -> ([TypeVar],[Type],[TypeVar],[TypeVar])
conScheme scheme
  = let (tvs,rho)    = splitScheme scheme
        (fields,res) = case rho of
                         TFun ps _ r -> (map snd ps, r)
                         r           -> ([], r)
        params       = [tv | TVar tv <- resultArgs res, tvarStar tv]
        exists       = [tv | tv <- tvs, tvarStar tv, not (tvarId tv `elem` map tvarId params)]
    in (tvs,fields,params,exists)

splitScheme :: Type -> ([TypeVar],Type)
splitScheme tp
  = case tp of
      TForall tvs t -> (tvs,expandSyn t)
      TSyn _ _ t    -> splitScheme t
      _             -> ([],expandSyn tp)

resultArgs :: Type -> [Type]
resultArgs tp
  = case expandSyn tp of
      TApp _ args -> args
      _           -> []

conExists :: ConInfo -> [TVar]
conExists con = let (_,_,_,exists) = conScheme (conInfoType con) in map tvarId exists

conShape :: Newtypes -> [VType] -> ConInfo -> Tr AType
conShape nt vargs con
  | null (conInfoParams con) = Right AUnit
  | otherwise = ABox <$> conValueFields nt vargs con

conCount :: DataInfo -> Int
conCount = length . dataInfoConstrs

conIndex :: DataInfo -> Name -> Tr Int
conIndex info cname
  = maybe (Left ("unknown constructor: " ++ show cname)) Right
          (elemIndex cname (map conInfoName (dataInfoConstrs info)))

refBody :: Newtypes -> DataInfo -> Tr (Maybe AType)
refBody nt info
  | dataDefIsOpen (dataInfoDef info) || null (dataInfoConstrs info) = Right Nothing
  | otherwise = Just . foldr1 ASum <$> mapM (conShape nt vargs) (dataInfoConstrs info)
  where
    vargs = map (VVar . tvarId) (filter tvarStar (dataInfoParams info))

typeDefs :: Platform -> Newtypes -> TypeDefs
typeDefs platform nt
  = M.fromList [(dataInfoName info, d) | (_,info) <- NM.toList (newtypesTypeDefs nt), not (isValueInfo info), Right d <- [typeDef platform nt info]]

typeDef :: Platform -> Newtypes -> DataInfo -> Tr TypeDef
typeDef platform nt info
  = do body <- refBody nt info
       return (TypeDef (dataInfoName info) (map tvarId (filter tvarStar (dataInfoParams info))) body (lazyInfo platform info))

lazyInfo :: Platform -> DataInfo -> Maybe LazyInfo
lazyInfo platform info
  = case [i | (i,con) <- zip [0..] cons, isLazyIndirectConName (conInfoName con)] of
      (i:_) -> Just (LazyInfo i [(conInfoIsLazy con, conReprAllocSize platform (getConRepr info con)) | con <- cons])
      []    -> Nothing
  where
    cons = dataInfoConstrs info
