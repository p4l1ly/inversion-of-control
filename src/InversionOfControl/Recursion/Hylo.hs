{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.Recursion.Hylo where

import Data.Monoid
import Data.Kind
import Control.Monad

data E (k :: Type) (af :: Type -> Type) (p :: Type) (r :: Type) (b :: Type) (m :: Type -> Type)

type family Af e :: Type -> Type where
  Af (E _ af _ _ _ _) = af
type family P e :: Type where
  P (E _ _ p _ _ _) = p
type family R e :: Type where
  R (E _ _ _ r _ _) = r
type family B e :: Type where
  B (E _ _ _ _ b _) = b
type family M e :: Type -> Type where
  M (E _ _ _ _ _ m) = m

class (Monad (M e), Applicative (Af e)) ⇒ Hylo e where
  hylo
    :: Endo (P e -> R e -> Af e (B e))
    -> M e (P e -> R e -> Af e (B e))

newtype BeforeAfter m a = BeforeAfter (m (m a))

instance Functor m ⇒ Functor (BeforeAfter m) where
  fmap f (BeforeAfter bef) = BeforeAfter (fmap (fmap f) bef)

instance Applicative m ⇒ Applicative (BeforeAfter m) where
  pure a = BeforeAfter (pure (pure a))
  BeforeAfter bef1 <*> BeforeAfter bef2 = BeforeAfter $ (<*>) <$> bef1 <*> bef2

runBeforeAfter ∷ Monad m ⇒ BeforeAfter m a → m a
runBeforeAfter (BeforeAfter bef) = join bef
