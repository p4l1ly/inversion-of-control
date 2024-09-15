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
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE UndecidableInstances #-}

module InversionOfControl.ExplicitMonadFn where

import Control.Monad.Trans (MonadTrans (lift))
import Data.Kind
import InversionOfControl.Lift (K (K), Pean (Succ, Zero), Unwrap)
import InversionOfControl.TypeDict
import GHC.TypeLits (Symbol)

class Monad m ⇒ MonadFn0 (k ∷ Type) (a :: Type) (b :: Type) (m ∷ Type → Type) where
  monadfn0 ∷ a → m b

class Monad m ⇒ MonadFn (k ∷ K) (a :: Type) (b :: Type) (m ∷ Type → Type) where
  monadfn ∷ a → m b

data E (d :: Type) (key :: Symbol) (a :: Type) (b :: Type) (m :: Type -> Type)
type family A (e :: Type) :: Type where
  A (E _ _ a _ _) = a
type family B (e :: Type) :: Type where
  B (E _ _ _ b _) = b
type family M (e :: Type) :: Type -> Type where
  M (E _ _ _ _ m) = m

class Monad (M e) ⇒ DMonadFn (e :: Type) where
  dmonadfn ∷ (A e) → M e (B e)

instance
  ( k ~ 'K (LiftsUntil key (Follow d)) (Get key (Follow d))
  , MonadFn k a b m
  , Monad m
  ) => DMonadFn (E d key a b m)
 where
  dmonadfn = monadfn @k

instance MonadFn0 k a b m ⇒ MonadFn ('K Zero k) a b m where
  monadfn ∷ a → m b
  monadfn = monadfn0 @k

instance
  (MonadFn ('K n k) a b m, MonadTrans mt, Monad m, Monad (mt m))
  ⇒ MonadFn ('K (Succ n) k) a b (mt m)
  where
  monadfn p1 = lift (monadfn @('K n k) p1)
