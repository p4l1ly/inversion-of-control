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
import qualified InversionOfControl.Recursion as R
import Control.Monad.Reader
import Data.Kind

data Rec

instance Applicative mb => KFn (R.RecE nb Rec p xb mb xb) where
  kfn _ = pure
