{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin2 #-}

module Main where

import InversionOfControl.TypeDict
import Data.Kind
import GHC.TypeLits

data DictD
data DictC

type instance DictDef DictC =
  Name "other" (Num Bool)
    :+: End

type instance DictDef DictD =
  Name "x" Int
    :+: End

main :: IO ()
main = fun

fun :: ToConstraintCached DictC => IO ()
fun = return ()
