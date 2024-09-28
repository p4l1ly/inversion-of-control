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

module InversionOfControl.MonadFn where

import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift (K, Succ, Zero)
import InversionOfControl.TypeDict
import InversionOfControl.GMonadTrans

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
  (MonadFn (E (K n k) a b m), GMonadTrans mt m, Monad mt, Monad m)
  ⇒ MonadFn (E (K (Succ n) k) a b mt)
  where
  monadfn p1 = glift (monadfn @(E (K n k) a b m) p1)

class (Monad (M e)) ⇒ MonadFnN (e ∷ Type) where
  monadfnn ∷ A e → M e (B e)

-- TODO The following should be implemented for all keys that implement MonadFn
-- and we should call only monadfnn, never monadfn.
--
-- instance (Monad (M e), MonadFn e) => MonadFnN e where
--   monadfnn = monadfn @e
