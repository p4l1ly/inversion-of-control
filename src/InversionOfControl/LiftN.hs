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

module InversionOfControl.LiftN where

import InversionOfControl.GMonadTrans
import Data.Kind
import InversionOfControl.Lift (Succ, Zero)

class LiftN (n ∷ Type) (m ∷ Type → Type) (m' ∷ Type → Type) | m' n -> m where
  liftn ∷ m a → m' a

instance (LiftN n m m', GMonadTrans mt m', Monad m') ⇒ LiftN (Succ n) m mt where
  liftn (ma ∷ m a) = glift (liftn @n @m @m' ma ∷ m' a)

instance LiftN Zero m m where
  liftn = id
