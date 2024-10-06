{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.KFn where

import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift (K, Succ, Zero)
import InversionOfControl.TypeDict
import InversionOfControl.GMonadTrans

class KFn (k ∷ Type) (d :: Type) where
  kfn :: [f|kfn|]

class KFnAuto (k :: Type) (d :: Type) where
  kfnAuto ∷ [f|kfn|]

instance
  ( KFnAuto (K n k) (UnliftD d)
  , [f|kfn|] ~ ([f|x|] -> [fk|m|] [f|y|])
  , GMonadTrans [fk|m|]
  , Monad [fk|m|]
  , Monad (Unlift [fk|m|])
  )
  ⇒ KFnAuto (K (Succ n) k) d
  where
  kfnAuto x = glift (kfnAuto @(K n k) @(UnliftD d) x)

data UnliftD d
type instance Definition (UnliftD d) =
  Name "kfn" ([f|x|] -> Unlift [fk|m|] [f|y|]) :+: Follow d
