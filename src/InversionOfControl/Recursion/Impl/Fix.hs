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

module InversionOfControl.Recursion.Impl.Fix where

import Data.Monoid
import Data.Fix
import Control.Monad.Identity
import qualified InversionOfControl.Recursion.Cata as C
import qualified InversionOfControl.Recursion.Hylo as H
import InversionOfControl.Lift
import InversionOfControl.LiftN

data FixK
type instance C.T (C.E (K n FixK) r fr b p m) = IdentityT
instance (Traversable f, Monad m) ⇒ C.Cata (C.E (K n FixK) (Fix f) (f (Fix f)) b p m)
  where
  cata algebra body = runIdentityT do
    let rec p r@(Fix fr) = algebra rec p r fr
    body rec

instance (Traversable f, Monad m, Applicative af) =>
  H.Hylo (H.E (K n FixK) af (Fix f) b p m)
  where
  hylo algebra = do
    let rec r p = appEndo algebra rec r p
    return rec
