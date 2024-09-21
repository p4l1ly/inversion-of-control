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

module InversionOfControl.Recursion.Impl.Free where

import Control.Monad.Free
import Control.Monad.Identity
import qualified InversionOfControl.Recursion.Cata as C
import qualified InversionOfControl.Recursion.Hylo as H
import InversionOfControl.Lift
import InversionOfControl.LiftN

data FreeK
type instance C.T (C.E (K n FreeK) r fr b p m) = IdentityT
instance (Traversable f, Monad m) ⇒ C.Cata (C.E (K n FreeK) (Free f b) (f (Free f b)) b p m)
  where
  cata algebra body = runIdentityT do
    let rec p r@(Free fr) = algebra rec p r fr
        rec p (Pure b) = return b
    body rec

instance (Traversable f, Monad m, Applicative af) =>
  H.Hylo (H.E (K n FreeK) af (Free f b) (f (Free f b)) b p m)
  where
  hylo algebra = do
    let rec (Free fr) p = algebra rec fr p
        rec (Pure b) p = pure b
    return rec
