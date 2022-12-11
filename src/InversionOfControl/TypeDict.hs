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
import Language.Haskell.TH (Exp (AppTypeE, VarE), TyLit (StrTyLit), Type (AppT, ConT, LitT, VarT), lookupTypeName, lookupValueName)
import Language.Haskell.TH.Quote (QuasiQuoter (..))

data Named k = Name Symbol k

data TypeDict where
  (:+:) :: Named k -> TypeDict -> TypeDict
  (:-:) :: Symbol -> TypeDict -> TypeDict
  End :: TypeDict
infixr 1 :+:
infixr 1 :-:

type family ToConstraint (dict :: TypeDict) :: Constraint where

type family Get (key :: Symbol) (dict :: TypeDict) :: k where

type family Definition (d :: *) :: k

type family Follow :: * -> k

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
