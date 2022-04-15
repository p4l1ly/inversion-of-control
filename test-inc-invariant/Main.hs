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
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin2 #-}
{-# OPTIONS_GHC -fplugin-opt InversionOfControl.TcPlugin2:no_getK_singletonDataCon #-}

module Main where

import Control.Monad.Identity (IdentityT (runIdentityT))
import InversionOfControl.Lift (Inc, K (K), Mk, Pean (Zero), Unwrap)
import InversionOfControl.MonadFn (Explicit, MonadFn (monadfn), Param, Result)
import InversionOfControl.TypeDict (GetK, Named (Name), TypeDict (End, (:+:)), d, d', LiftTags, ToConstraint)

data Even
type instance Param Even = Int
type instance Result Even = Bool

instance MonadFn ( 'K Zero Even) IO where
  monadfn x = print (even x) >> return (even x)

data Odd
type instance Param Odd = Int
type instance Result Odd = Bool

instance MonadFn ( 'K Zero Odd) IO where
  monadfn x = print ("hii", odd x) >> return (odd x)

main :: IO ()
main = do
  False <- hardFunction @(Name "k01" ( 'K Zero Even) :+: End)
  True <- hardFunction @(Name "k01" ( 'K Zero Odd) :+: End)
  return ()

hardFunction ::
  forall d d' n t.
  ( d' ~ (Name "k03" [d|k01|] :+: Name "k02" [d|k01|] :+: End)
  , [d'|k02|] ~ 'K n t  -- TODO remove after plugin fix
  , ToConstraint (Name "foo" (MonadFn [d'|k02|] IO) :+: End)
  -- , MonadFn [d'|k02|] IO
  , Int ~ Param (Unwrap [d'|k02|])
  , Bool ~ Result (Unwrap [d'|k02|])
  ) =>
  IO Bool
hardFunction = do
  monadfn @[d'|k02|] 5
  runIdentityT $ monadfn @(GetK "k02" (LiftTags d')) 5
