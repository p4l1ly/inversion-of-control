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
import Control.Monad.Identity (IdentityT (runIdentityT))
import InversionOfControl.Lift (Inc, K (K), Inherit, Pean (Succ, Zero), Unwrap)
import InversionOfControl.MonadFn (Explicit, MonadFn (monadfn), MonadFn0 (monadfn0), Param, Result)
import InversionOfControl.TypeDict
  ( Get
  , Named (Name)
  , TypeDict (End, (:+:), (:-:))
  , g, g1
  , ToConstraint
  , Definition
  , Follow
  )
import GHC.Types (Constraint)

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

data EvenDict (lifts :: Pean)
type instance Definition (EvenDict lifts) =
  Name "k01" ('K lifts Even) :+: End

data OddDict (lifts :: Pean)
type instance Definition (OddDict lifts) =
  Name "k01" ('K lifts Odd) :+: End

main :: IO ()
main = do
  (False, True, True) <- highFn @EvenDict
  (True, False, False) <- highFn @OddDict
  return ()

data HighFnA (d :: *)
type instance Definition (HighFnA d) =
  -- Kinds must be specified, otherwise weird things happen
  -- (including core lint warnings).
  ( Name "k03" ([g|k01|] :: K)
    :+: Name "k02" (Get "k03" (Follow (HighFnA d)) :: K)
    :+: End
  )

data HighFnI (d :: Pean -> *) (d1 :: *) (m :: * -> *) :: *
type instance Definition (HighFnI d d1 m) =
  ( Name "all"
      ( d1 ~ HighFnA (d Zero)
      , MonadFn ([g1|k02|] :: K) m
      , Int ~ Param (Unwrap [g1|k02|])
      , Bool ~ Result (Unwrap [g1|k02|])
      )
      -- Properly written code would also include:
      --   Follow (LowFnD (d Zero) m)
      -- But it is logically not a bug to omit it, as LowFnD is implied by
      -- HighFnD. We omit it here for testing purposes.
      :+: Follow (LowFnD (d (Succ Zero)) (IdentityT m))
  )

type HighFnD (d :: Pean -> *) (m :: * -> *) =
  HighFnI d (HighFnA (d Zero)) m

highFn ::
  forall d d1 m.
  ToConstraint (Follow (HighFnI d d1 m)) =>
  m (Bool, Bool, Bool)
highFn = do
  (,,)
    <$> monadfn @[g1|k02|] 5
    <*> lowFn @(d Zero)
    <*> runIdentityT (lowFn @(d (Succ Zero)))

data LowFnI (d :: *) (m :: * -> *) :: *
type instance Definition (LowFnI d m) =
  ( Name "all"
      ( MonadFn [g|k01|] m
      , Int ~ Param (Unwrap [g|k01|])
      , Bool ~ Result (Unwrap [g|k01|])
      )
      :+: End
  )

type LowFnD d m = LowFnI d m

lowFn ::
  forall d m.
  ToConstraint (Follow (LowFnI d m)) =>
  m Bool
lowFn = monadfn @[g|k01|] 6
