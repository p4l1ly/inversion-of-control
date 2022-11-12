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
import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift (Inc, K (K), Pean (Zero))
import Language.Haskell.TH (Exp (AppTypeE, VarE), TyLit (StrTyLit), Type (AppT, ConT, LitT, VarT), lookupTypeName, lookupValueName)
import Language.Haskell.TH.Quote (QuasiQuoter (..))

data Named x = Name Symbol x

data TypeDict where
  End :: TypeDict
  (:+:) :: Named x -> TypeDict -> TypeDict
infixr 1 :+:

type family GetK (sym :: Symbol) (dict :: TypeDict) :: K where

type family LiftTags (dict :: TypeDict) :: TypeDict where

type family Remove (sym :: Symbol) (dict :: TypeDict) :: TypeDict where

type family ToConstraint (dict :: TypeDict) :: Constraint where

type family Get (sym :: Symbol) (dict :: TypeDict) :: k where -- TODO doesn't work through LiftTags, need to include into TcPlugin

type family DictDef (d :: *) :: TypeDict

data KArg (k :: Symbol)

type family ToConstraintCached (constrs :: *) (defs :: *) :: Constraint where

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
