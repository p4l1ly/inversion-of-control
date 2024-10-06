{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.Recursion where

import InversionOfControl.TypeDict
import InversionOfControl.KFn

data Recur d
type instance Definition (Recur d) =
  Name "x" ([f|p|] -> [f|r|] -> [f|a|] -> [f|b|], [f|p|], [f|r|])
  :+: Name "kfn" ([fs|x|] -> [f|b|])
  :+: Follow d
