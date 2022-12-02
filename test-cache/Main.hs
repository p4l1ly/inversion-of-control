{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import InversionOfControl.TypeDict
import Data.Kind
import GHC.TypeLits

data DictD
data DictC (d :: *)

type instance Definition (DictC d) =
  Name "other" (Num Bool)
    :+: End

type instance Definition DictD =
  Name "x" Int
    :+: End

main :: IO ()
main = fun @DictD

fun :: forall d. ToConstraint (Follow (DictC d)) => IO ()
fun = return ()
