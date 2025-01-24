{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module InversionOfControl.LiftN where

import InversionOfControl.GMonadTrans
import Data.Kind
import InversionOfControl.Lift (Succ, Zero)

class LiftN (n ∷ Type) (m ∷ Type → Type) (m' ∷ Type → Type) | m' n -> m where
  liftn ∷ m a → m' a

instance (LiftN n m (Unlift mt), GMonadTrans mt, Monad (Unlift mt)) ⇒ LiftN (Succ n) m mt where
  liftn (ma ∷ m a) = glift (liftn @n @m @(Unlift mt) ma ∷ Unlift mt a)

instance LiftN Zero m m where
  liftn = id

type family UnliftN (n ∷ Type) (m ∷ Type → Type) :: Type → Type where
  UnliftN Zero m = m
  UnliftN (Succ n) m = Unlift (UnliftN n m)
