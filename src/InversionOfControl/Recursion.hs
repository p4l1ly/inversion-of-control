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
{-# LANGUAGE AllowAmbiguousTypes #-}

module InversionOfControl.Recursion where

import InversionOfControl.TypeDict
import InversionOfControl.KFn

type Recur p r a b = (p -> r -> a -> b) -> p -> r -> b
type Cata r a b = (a -> b) -> r -> b

type RecurE n k p r a b = KE n k (Recur p r a b)
type CataE n k r a b = RecurE n k () r a b

cata :: forall e n k r a b c. (e ~ CataE n k r a b, KFn e) => Cata r a b
cata algebra = kfn @e (\_ _ -> algebra) ()
