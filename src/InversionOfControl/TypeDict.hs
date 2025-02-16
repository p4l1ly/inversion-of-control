{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.TypeDict where

import Data.Functor ((<&>))
import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift
import Language.Haskell.TH
  ( Exp (AppTypeE, VarE)
  , TyLit (StrTyLit)
  , lookupTypeName
  , lookupValueName
  , pattern AppT
  , pattern ConT
  , pattern LitT
  , pattern VarT
  )
import Language.Haskell.TH.Quote (QuasiQuoter (..))

data Name (key ∷ Symbol) (val ∷ Type)

data (:+:) ∷ Type → Type → Type
data End ∷ Type
infixr 1 :+:

type family ToConstraint (dict ∷ Type) ∷ Constraint where

type family WaitPlugin (a ∷ Type) ∷ Type where

type family Definition (d ∷ Type) ∷ k

type family GetFam (key ∷ Symbol) (dict ∷ Type) ∷ Type where

type family Unkindy (f ∷ Type) ∷ k where
  Unkindy (Kindy f) = f

data Self
data Follow (def ∷ Type)
data LiftsUntil (key ∷ Symbol) (dict ∷ Type)
data Get (key ∷ Symbol) (dict ∷ Type)
data ConstraintVal (constr ∷ Constraint)
data Kindy (f :: k)


data LiftUp d
type instance Definition (LiftUp d) = Name "lift" () :+: Follow d

data Empty
type instance Definition Empty = End

g ∷ QuasiQuoter
g =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d"
        case d of
          Just d → return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing → error "g: type d not in scope"
    , quoteExp = error "g can quote only types"
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }

f ∷ QuasiQuoter
f =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d"
        case d of
          Just d → return $ AppT (AppT (ConT ''GetFam) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing → error "g: type d not in scope"
    , quoteExp = error "g can quote only types"
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }

fk ∷ QuasiQuoter
fk =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d"
        case d of
          Just d → return $ AppT (ConT ''Unkindy) (AppT (AppT (ConT ''GetFam) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
          Nothing → error "g: type d not in scope"
    , quoteExp = error "g can quote only types"
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }

g1 ∷ QuasiQuoter
g1 =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d1"
        case d of
          Just d → return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing → error "g1: type d1 not in scope"
    , quoteExp = error "g1 can quote only types"
    , quoteDec = error "g1 can quote only types"
    , quotePat = error "g1 can quote only types"
    }

g2 ∷ QuasiQuoter
g2 =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d2"
        case d of
          Just d → return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d))
          Nothing → error "g2: type d2 not in scope"
    , quoteExp = error "g2 can quote only types"
    , quoteDec = error "g2 can quote only types"
    , quotePat = error "g2 can quote only types"
    }

-- TODO is this useful?
gc ∷ QuasiQuoter
gc =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d"
        c ← lookupTypeName "cont"
        case (d, c) of
          (Just d, Just c) →
            return $
              AppT
                (AppT (ConT ''Get) (LitT (StrTyLit tag)))
                (AppT (ConT ''Follow) (AppT (VarT d) (VarT c)))
          _ → error "gc: type d, cont or n not in scope"
    , quoteExp = error "gc can quote only types"
    , quoteDec = error "gc can quote only types"
    , quotePat = error "gc can quote only types"
    }

gs ∷ QuasiQuoter
gs =
  QuasiQuoter
    { quoteType = \tag → do
        return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (ConT ''Self))
    , quoteExp = error "gs can quote only types"
    , quoteDec = error "gs can quote only types"
    , quotePat = error "gs can quote only types"
    }

fs ∷ QuasiQuoter
fs =
  QuasiQuoter
    { quoteType = \tag → do
        return $ AppT (AppT (ConT ''GetFam) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (ConT ''Self))
    , quoteExp = error "gs can quote only types"
    , quoteDec = error "gs can quote only types"
    , quotePat = error "gs can quote only types"
    }

fsk ∷ QuasiQuoter
fsk =
  QuasiQuoter
    { quoteType = \tag → do
        return $ AppT (ConT ''Unkindy) (AppT (AppT (ConT ''GetFam) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (ConT ''Self)))
    , quoteExp = error "gs can quote only types"
    , quoteDec = error "gs can quote only types"
    , quotePat = error "gs can quote only types"
    }

k ∷ QuasiQuoter
k =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d"
        case d of
          Just d →
            return $
              AppT
                ( AppT
                    (ConT ''K)
                    (AppT (AppT (ConT ''LiftsUntil) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
                )
                (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
          Nothing → error "k: type d not in scope"
    , quoteExp = error "k can quote only types"
    , quoteDec = error "k can quote only types"
    , quotePat = error "k can quote only types"
    }

e ∷ QuasiQuoter
e =
  QuasiQuoter
    { quoteType = \eetag → do
        let (eename, _:tag) = break (== '|') eetag
        ee <- lookupTypeName eename
        d ← lookupTypeName "d"
        case (d, ee) of
          (Just d, Just ee) →
            return $
              AppT
                ( AppT
                    (ConT ee)
                    (AppT (AppT (ConT ''LiftsUntil) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
                )
                (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
          (Nothing, _) → error "e: type d not in scope"
          _ -> error $ "e: type " ++ eename ++ " not in scope"
    , quoteExp = error "k can quote only types"
    , quoteDec = error "k can quote only types"
    , quotePat = error "k can quote only types"
    }

k1 ∷ QuasiQuoter
k1 =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d1"
        case d of
          Just d →
            return $
              AppT
                ( AppT
                    (ConT ''K)
                    (AppT (AppT (ConT ''LiftsUntil) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
                )
                (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
          Nothing → error "k1: type d1 not in scope"
    , quoteExp = error "k1 can quote only types"
    , quoteDec = error "k1 can quote only types"
    , quotePat = error "k1 can quote only types"
    }

k2 ∷ QuasiQuoter
k2 =
  QuasiQuoter
    { quoteType = \tag → do
        d ← lookupTypeName "d2"
        case d of
          Just d →
            return $
              AppT
                ( AppT
                    (ConT ''K)
                    (AppT (AppT (ConT ''LiftsUntil) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
                )
                (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (VarT d)))
          Nothing → error "k2: type d2 not in scope"
    , quoteExp = error "k2 can quote only types"
    , quoteDec = error "k2 can quote only types"
    , quotePat = error "k2 can quote only types"
    }

ks ∷ QuasiQuoter
ks =
  QuasiQuoter
    { quoteType = \tag → do
        return $
          AppT
            ( AppT
                (ConT ''K)
                (AppT (AppT (ConT ''LiftsUntil) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (ConT ''Self)))
            )
            (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (AppT (ConT ''Follow) (ConT ''Self)))
    , quoteExp = error "ks can quote only types"
    , quoteDec = error "ks can quote only types"
    , quotePat = error "ks can quote only types"
    }
