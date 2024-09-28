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

module InversionOfControl.Recursion.Fix where

import Data.Monoid
import Data.Fix
import InversionOfControl.Recursion
import InversionOfControl.Lift

data Rec
instance (Traversable f, Monad m) ⇒ Recur (E (K n Rec) p (Fix f) (f (Fix f)) b m m)
  where
  recur algebra act = do
    let rec p r@(Fix a) = algebra rec p r a
    act rec
