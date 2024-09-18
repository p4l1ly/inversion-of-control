{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.ExplicitMonadFn where

import Control.Monad.Trans (MonadTrans (lift))
import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift (K, Succ, Zero)
import InversionOfControl.TypeDict

class Monad (M e) ⇒ MonadFn (e ∷ Type) where
  monadfn ∷ A e → M e (B e)

data E (key ∷ Type) (a ∷ Type) (b ∷ Type) (m ∷ Type → Type)
type family A (e ∷ Type) ∷ Type where
  A (E _ a _ _) = a
type family B (e ∷ Type) ∷ Type where
  B (E _ _ b _) = b
type family M (e ∷ Type) ∷ Type → Type where
  M (E _ _ _ m) = m

instance
  (MonadFn (E (K n k) a b m), MonadTrans mt, Monad m, Monad (mt m))
  ⇒ MonadFn (E (K (Succ n) k) a b (mt m))
  where
  monadfn p1 = lift (monadfn @(E (K n k) a b m) p1)
