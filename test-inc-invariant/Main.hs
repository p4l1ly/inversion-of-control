{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}

module Main where

import Control.Monad.Identity
import Control.Monad.Trans
import Data.Kind
import GHC.Types
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import InversionOfControl.ExplicitMonadFn

data Even
instance MonadFn (E (K Zero Even) Int Bool IO) where
  monadfn x = print ("even", x, even x) >> return (even x)

data Odd
instance MonadFn (E (K Zero Odd) Int Bool IO) where
  monadfn x = print ("odd", x, odd x) >> return (odd x)

data EvenDict
type instance
  Definition EvenDict =
    Name "k01" Even :+: End

data OddDict
type instance
  Definition OddDict =
    Name "k01" Odd :+: End

main ∷ IO ()
main = do
  (False, True, True) ← highFn @EvenDict
  (True, False, False) ← highFn @OddDict
  return ()

data HighFnA (d ∷ Type)
type instance
  Definition (HighFnA d) =
    Name "k03" [k|k01|]
      :+: Name "k02" [gs|k03|]
      :+: End

type EHigh d m = E [g|k02|] Int Bool m
type HighFnI (d ∷ Type) (d1 ∷ Type) (m ∷ Type → Type) =
  ( d1 ~ HighFnA d
  , MonadFn (EHigh d1 m)
  , Monad m
  -- Commonly, we would add also the following constraints but in this case they can be inferred,
  -- so we omit them to show that inference works.
  -- , LowFnD (LiftUp d) (IdentityT m)
  -- , LowFnD d m
  )
    ∷ Constraint
type HighFnD (d ∷ Type) (m ∷ Type → Type) = HighFnI d (HighFnA d) m

highFn ∷ ∀ d d1 m. HighFnI d d1 m ⇒ m (Bool, Bool, Bool)
highFn = do
  (,,)
    <$> monadfn @(EHigh d1 m) 5
    <*> runIdentityT (lowFn @(LiftUp d))
    <*> lowFn @d

type ELow d m = E [k|k01|] Int Bool m
type LowFnD (d :: Type) (m :: Type -> Type) = MonadFn (ELow d m)

lowFn ∷ ∀ d m. LowFnD d m ⇒ m Bool
lowFn = monadfn @(ELow d m) 6
