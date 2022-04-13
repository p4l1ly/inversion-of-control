{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module InversionOfControl.TypeDict where

import Data.Functor ((<&>))
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift (Inc, K)
import Language.Haskell.TH (Exp (AppTypeE, VarE), TyLit (StrTyLit), Type (AppT, ConT, LitT, VarT), lookupTypeName, lookupValueName)
import Language.Haskell.TH.Quote (QuasiQuoter (..))

data NotFound (k :: Symbol)
data Named x = Name Symbol x

data TypeDict where
  End :: TypeDict
  (:+:) :: Named x -> TypeDict -> TypeDict
  LiftTags :: TypeDict -> TypeDict
infixr 1 :+:

type family GetK (sym :: Symbol) (dict :: TypeDict) :: K where
  GetK sym (LiftTags rest) = Inc (GetK sym rest)
  GetK sym (Name sym val :+: rest) = val
  GetK sym (_ :+: rest) = GetK sym rest

type family Get (sym :: Symbol) (dict :: TypeDict) :: k where
  Get sym End = NotFound sym
  Get sym (LiftTags rest) = Get sym rest
  Get sym (Name sym val :+: rest) = val
  Get sym (_ :+: rest) = Get sym rest

d :: QuasiQuoter
d =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        case d of
          Just d -> return $ AppT (AppT (ConT ''GetK) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "d: type d not in scope"
    , quoteExp = \str -> do
        let (fnName, '|' : tag) = break (== '|') str
        d <- lookupTypeName "d"
        fn <- lookupValueName fnName
        case (d, fn) of
          (Nothing, _) -> error "d: type d not in scope"
          (_, Nothing) -> error $ "d: function " ++ fnName ++ " not in scope"
          (Just d, Just fn) ->
            return $
              AppTypeE (VarE fn) (AppT (AppT (ConT ''GetK) (LitT (StrTyLit tag))) (VarT d))
    , quoteDec = error "d can quote only types"
    , quotePat = error "d can quote only types"
    }

d' :: QuasiQuoter
d' =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d'"
        case d of
          Just d -> return $ AppT (AppT (ConT ''GetK) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "d': type d' not in scope"
    , quoteExp = \str -> do
        let (fnName, '|' : tag) = break (== '|') str
        d <- lookupTypeName "d'"
        fn <- lookupValueName fnName
        case (d, fn) of
          (Nothing, _) -> error "d': type d' not in scope"
          (_, Nothing) -> error $ "d': function " ++ fnName ++ " not in scope"
          (Just d, Just fn) ->
            return $
              AppTypeE (VarE fn) (AppT (AppT (ConT ''GetK) (LitT (StrTyLit tag))) (VarT d))
    , quoteDec = error "d' can quote only types"
    , quotePat = error "d' can quote only types"
    }

g :: QuasiQuoter
g =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "g: type d not in scope"
    , quoteExp = error "g can quote only types"
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }

g' :: QuasiQuoter
g' =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d'"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "g': type d' not in scope"
    , quoteExp = error "g can quote only types"
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }
