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
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}

module Main where

import Control.Monad.Trans
import Control.Monad.Identity
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import GHC.Types
import Data.Kind

data Even
type instance Param Even = Int
type instance Result Even = Bool

instance MonadFn0 Even IO where
  monadfn0 x = print ("even", x, even x) >> return (even x)

data Odd
type instance Param Odd = Int
type instance Result Odd = Bool

instance MonadFn0 Odd IO where
  monadfn0 x = print ("odd", x, odd x) >> return (odd x)

data EvenDict
type instance Definition EvenDict =
  Name "k01" Even :+: End

data OddDict
type instance Definition OddDict =
  Name "k01" Odd :+: End

main :: IO ()
main = do
  (False, True, True) <- highFn @EvenDict
  (True, False, False) <- highFn @OddDict
  return ()

data HighFnA (d :: Type)
type instance Definition (HighFnA d) =
  -- Kinds must be specified, otherwise weird things happen
  -- (including core lint warnings).
  ( Name "k03" ([k|k01|] :: K)
    :+: Name "k02" ([gs|k03|] :: K)
    :+: End
  )

data HighFnI (d :: Type) (d1 :: Type) (m :: Type -> Type) :: Type
type instance Definition (HighFnI d d1 m) =
  ( Name "all"
      ( d1 ~ HighFnA d
      , MonadFn [g1|k02|] m
      , Int ~ Param (Unwrap [g1|k02|])
      , Bool ~ Result (Unwrap [g1|k02|])
      )
      -- Properly written code would also include:
      --   Follow (LowFnD d m)
      -- But it is logically not a bug to omit it, as LowFnD is implied by
      -- HighFnD. We omit it here for testing purposes.
      :+: End
  )

type HighFnD (d :: Type) (m :: Type -> Type) =
  HighFnI d (HighFnA d) m

highFn ::
  forall d d1 m.
  ToConstraint (Follow (HighFnI d d1 m)) =>
  m (Bool, Bool, Bool)
highFn = do
  (,,)
    <$> monadfn @[g1|k02|] 5
    <*> lowFn @d
    <*> runIdentityT (lowFn @(LiftUp d))

data LowFnI (d :: Type) (m :: Type -> Type) :: Type
type instance Definition (LowFnI d m) =
  ( Name "all"
      ( MonadFn [k|k01|] m
      , Int ~ Param (Unwrap [k|k01|])
      , Bool ~ Result (Unwrap [k|k01|])
      )
      :+: End
  )

type LowFnD d m = LowFnI d m

lowFn ::
  forall d m.
  ToConstraint (Follow (LowFnI d m)) =>
  m Bool
lowFn = monadfn @[k|k01|] 6
