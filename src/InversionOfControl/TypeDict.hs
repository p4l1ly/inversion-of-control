{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module InversionOfControl.TypeDict where

import Data.Functor ((<&>))
import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift
import Language.Haskell.TH (Exp (AppTypeE, VarE), TyLit (StrTyLit), Type (AppT, ConT, LitT, VarT), lookupTypeName, lookupValueName)
import Language.Haskell.TH.Quote (QuasiQuoter (..))

data Named k = Name Symbol k

data TypeDict where
  (:+:) :: Named k -> TypeDict -> TypeDict
  End :: TypeDict
infixr 1 :+:

type family ToConstraint (dict :: TypeDict) :: Constraint where

type family Get (key :: Symbol) (dict :: TypeDict) :: k where

type family Self :: * where

type family Definition (d :: *) :: k

type family Follow :: * -> k

type family LiftsUntil (dict :: TypeDict) :: Pean

-- TODO Let solver know the following rule:
-- GetK key (d (Succ n)) = Inc (GetK key (d n))

g :: QuasiQuoter
g =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing -> error "g: type d not in scope"
    , quoteExp = error "g can quote only types"
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }

g1 :: QuasiQuoter
g1 =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d1"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing -> error "g1: type d1 not in scope"
    , quoteExp = error "g1 can quote only types"
    , quoteDec = error "g1 can quote only types"
    , quotePat = error "g1 can quote only types"
    }

g2 :: QuasiQuoter
g2 =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d2"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing -> error "g2: type d2 not in scope"
    , quoteExp = error "g2 can quote only types"
    , quoteDec = error "g2 can quote only types"
    , quotePat = error "g2 can quote only types"
    }

-- TODO is this useful?
gcn :: QuasiQuoter
gcn =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        c <- lookupTypeName "cont"
        n <- lookupTypeName "n"
        case (d, c, n) of
          (Just d, Just c, Just n) ->
            return $
              AppT
                (AppT (ConT ''Get) (LitT (StrTyLit tag)))
                (AppT (ConT ''Follow) (AppT (AppT (VarT d) (VarT c)) (VarT n)))
          _ -> error "gcn: type d, cont or n not in scope"
    , quoteExp = error "gcn can quote only types"
    , quoteDec = error "gcn can quote only types"
    , quotePat = error "gcn can quote only types"
    }

gs :: QuasiQuoter
gs =
  QuasiQuoter
    { quoteType = \tag -> do
        return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (ConT ''Self))
    , quoteExp = error "gs can quote only types"
    , quoteDec = error "gs can quote only types"
    , quotePat = error "gs can quote only types"
    }
