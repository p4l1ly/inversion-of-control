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
-- debug
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file -dcore-lint -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Control.Monad.Identity (IdentityT (runIdentityT))
import InversionOfControl.Lift (Inc, K (K), Mk, Pean (Zero), Unwrap)
import InversionOfControl.MonadFn (Explicit, MonadFn (monadfn), Param, Result)
import InversionOfControl.TypeDict (GetK, Named (Name), TypeDict (End, (:+:)), d, d')

data Even
type instance Param Even = Int
type instance Result Even = Bool

instance MonadFn ( 'K Zero Even) IO where
  monadfn x = print (even x) >> return (even x)

data Odd
type instance Param Odd = Int
type instance Result Odd = Bool

instance MonadFn ( 'K Zero Odd) IO where
  monadfn x = print ("hi", odd x) >> return (odd x)

main :: IO ()
main = do
  False <- hardFunction @(Name "k01" ( 'K Zero Even) :+: End)
  True <- hardFunction @(Name "k01" ( 'K Zero Odd) :+: End)
  return ()

hardFunction ::
  forall d n t.
  ( MonadFn [d|k01|] IO
  , -- , [d|k01|] ~ 'K n t -- TODO does not work without this
    Int ~ Param (Unwrap [d|k01|])
  , Bool ~ Result (Unwrap [d|k01|])
  ) =>
  IO Bool
hardFunction = do
  monadfn @(GetK "k01" d) 5
  runIdentityT $ monadfn @(Inc [d|k01|]) 5
