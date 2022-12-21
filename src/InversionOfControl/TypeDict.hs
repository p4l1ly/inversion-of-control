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

-- TODO Let solver know the following rule:
-- GetK key (d (Succ n)) = Inc (GetK key (d n))

d :: QuasiQuoter
d =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing -> error "d: type d not in scope"
    , quoteExp = error "d can quote only types"
    , quoteDec = error "d can quote only types"
    , quotePat = error "d can quote only types"
    }

d1 :: QuasiQuoter
d1 =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d1"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing -> error "g: type d1 not in scope"
    , quoteExp = error "d can quote only types"
    , quoteDec = error "d can quote only types"
    , quotePat = error "d can quote only types"
    }

d2 :: QuasiQuoter
d2 =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d2"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing -> error "g: type d2 not in scope"
    , quoteExp = error "d can quote only types"
    , quoteDec = error "d can quote only types"
    , quotePat = error "d can quote only types"
    }
