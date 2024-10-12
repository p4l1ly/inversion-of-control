{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module InversionOfControl.Recursion where

import InversionOfControl.TypeDict
import InversionOfControl.KFn

type Recur p r a b = ((p -> r -> a -> b) -> p -> r -> b)
type Cata r a b = ((a -> b) -> r -> b)

type RecurE n k p r a b = KE n k (Recur () r a b)
type CataE n k r a b = KE n (CataK k) (Cata r a b)

data CataK k
instance
  KFn (RecurE n k p r a b)
  => KFn (CataE n k r a b)
  where
  kfn algebra = kfn @(RecurE n k p r a b) (\_ _ -> algebra) ()
