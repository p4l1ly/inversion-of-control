{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.Recursion.Cata where

import Control.Monad.Trans
import Data.Kind
import InversionOfControl.LiftN
import Data.Monoid

data E (k ∷ Type) (r ∷ Type) (b :: Type) (p :: Type) (m :: Type -> Type)
type family R e ∷ Type where
  R (E _ r _ _ _) = r
type family B e ∷ Type where
  B (E _ _ b _ _) = b
type family P e ∷ Type where
  P (E _ _ _ p _) = p
type family M e ∷ Type -> Type where
  M (E _ _ _ _ m) = m

type family T (e ∷ Type) ∷ (Type → Type) → Type → Type

class (Monad (M e), MonadTrans (T e), Monad (T e (M e))) ⇒ Cata e where
  cata
    ∷ ∀ n m' a
     . (Monad m', LiftN n (T e (M e)) m')
    ⇒ Endo (P e -> R e → m' (B e))
    → M e (P e -> R e → m' (B e))
