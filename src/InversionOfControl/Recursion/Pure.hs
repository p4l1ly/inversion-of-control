{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}

module InversionOfControl.Recursion.Pure where

import Data.Fix
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.Recursion
import Control.Monad.Reader
import Data.Kind

type RecT p a b = ReaderT (p -> a -> b)

runRecursion
  :: RecT p a b m0 c
  -> (p -> a -> b)
  -> m0 c
runRecursion act algebra = runReaderT act algebra

-- type RecurC n0 nb mb xb p f =
--   ( Monad mb
--   , Monad (UnliftN (Succ nb) mb)
--   , LiftN nb (RecT p f (mb xb) (UnliftN (Succ nb) mb)) mb
--   ) :: Constraint

-- recur :: forall n0 nb mb xb p f a.
--   RecurC n0 nb mb xb p f => p -> Fix f -> mb xb
-- recur p r@(Fix fr) = do
--   algebra <- liftn @nb ask
--   algebra p r fr
