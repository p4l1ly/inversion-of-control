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

module InversionOfControl.Recursion.Pure where

import Data.Fix
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.Lift
import InversionOfControl.Recursion

data Go
instance
  Applicative m =>
  KFn (E (K n Go) (r -> m r))
  where
  kfn = pure

data Rec
instance
  Applicative m =>
  KFn (RecurE n Rec p r a (m r))
  where
  kfn _ _ r = pure r
