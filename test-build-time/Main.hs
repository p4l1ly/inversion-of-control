{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.Kind
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict

data Even
data Odd

instance MonadFn0 (Explicit Int Bool Even) IO where
  monadfn0 = return . even

instance MonadFn0 (Explicit Int Bool Odd) IO where
  monadfn0 = return . odd

data OptionsD

type instance
  Definition OptionsD =
    Name "k01" Even
      :+: Name "k02" Even
      :+: Name "k03" Even
      :+: Name "k04" Even
      :+: Name "k05" Even
      :+: Name "k06" Even
      :+: Name "k07" Even
      :+: Name "k08" Even
      :+: Name "k09" Even
      :+: Name "k10" Even
      :+: Name "k11" Even
      :+: Name "k12" Even
      :+: Name "k13" Even
      :+: Name "k14" Even
      :+: Name "k15" Even
      :+: Name "k16" Even
      :+: Name "k17" Even
      :+: Name "k18" Even
      :+: Name "k19" Even
      :+: Name "k20" Even
      :+: Name "k21" Even
      :+: Name "k22" Even
      :+: Name "k23" Even
      :+: Name "k24" Even
      :+: Name "k25" Even
      :+: Name "k26" Even
      :+: Name "k27" Even
      :+: Name "k28" Even
      :+: Name "k29" Even
      :+: Name "k30" Even
      :+: End

main ∷ IO ()
main = hardToCompileFn @OptionsD

data HardToCompileFnA (d ∷ Type)
type instance
  Definition (HardToCompileFnA d) =
    Name "k01" (Inherit (Explicit Int Bool) [k|k01|])
      :+: Name "k02" (Inherit (Explicit Int Bool) [k|k02|])
      :+: Name "k03" (Inherit (Explicit Int Bool) [k|k03|])
      :+: Name "k04" (Inherit (Explicit Int Bool) [k|k04|])
      :+: Name "k05" (Inherit (Explicit Int Bool) [k|k05|])
      :+: Name "k06" (Inherit (Explicit Int Bool) [k|k06|])
      :+: Name "k07" (Inherit (Explicit Int Bool) [k|k07|])
      :+: Name "k08" (Inherit (Explicit Int Bool) [k|k08|])
      :+: Name "k09" (Inherit (Explicit Int Bool) [k|k09|])
      :+: Name "k10" (Inherit (Explicit Int Bool) [k|k10|])
      :+: Name "k11" (Inherit (Explicit Int Bool) [k|k11|])
      :+: Name "k12" (Inherit (Explicit Int Bool) [k|k12|])
      :+: Name "k13" (Inherit (Explicit Int Bool) [k|k13|])
      :+: Name "k14" (Inherit (Explicit Int Bool) [k|k14|])
      :+: Name "k15" (Inherit (Explicit Int Bool) [k|k15|])
      :+: Name "k16" (Inherit (Explicit Int Bool) [k|k16|])
      :+: Name "k17" (Inherit (Explicit Int Bool) [k|k17|])
      :+: Name "k18" (Inherit (Explicit Int Bool) [k|k18|])
      :+: Name "k19" (Inherit (Explicit Int Bool) [k|k19|])
      :+: Name "k20" (Inherit (Explicit Int Bool) [k|k20|])
      :+: Name "k21" (Inherit (Explicit Int Bool) [k|k21|])
      :+: Name "k22" (Inherit (Explicit Int Bool) [k|k22|])
      :+: Name "k23" (Inherit (Explicit Int Bool) [k|k23|])
      :+: Name "k24" (Inherit (Explicit Int Bool) [k|k24|])
      :+: Name "k25" (Inherit (Explicit Int Bool) [k|k25|])
      :+: Name "k26" (Inherit (Explicit Int Bool) [k|k26|])
      :+: Name "k27" (Inherit (Explicit Int Bool) [k|k27|])
      :+: Name "k28" (Inherit (Explicit Int Bool) [k|k28|])
      :+: Name "k29" (Inherit (Explicit Int Bool) [k|k29|])
      :+: Name "k30" (Inherit (Explicit Int Bool) [k|k30|])
      :+: End

data HardToCompileFnD (d1 ∷ Type)
type instance
  Definition (HardToCompileFnD d1) =
    Name "k01" (MonadFn [g1|k01|] IO)
      :+: Name "k02" (MonadFn [g1|k02|] IO)
      :+: Name "k03" (MonadFn [g1|k03|] IO)
      :+: Name "k04" (MonadFn [g1|k04|] IO)
      :+: Name "k05" (MonadFn [g1|k05|] IO)
      :+: Name "k06" (MonadFn [g1|k06|] IO)
      :+: Name "k07" (MonadFn [g1|k07|] IO)
      :+: Name "k08" (MonadFn [g1|k08|] IO)
      :+: Name "k09" (MonadFn [g1|k09|] IO)
      :+: Name "k10" (MonadFn [g1|k10|] IO)
      :+: Name "k11" (MonadFn [g1|k11|] IO)
      :+: Name "k12" (MonadFn [g1|k12|] IO)
      :+: Name "k13" (MonadFn [g1|k13|] IO)
      :+: Name "k14" (MonadFn [g1|k14|] IO)
      :+: Name "k15" (MonadFn [g1|k15|] IO)
      :+: Name "k16" (MonadFn [g1|k16|] IO)
      :+: Name "k17" (MonadFn [g1|k17|] IO)
      :+: Name "k18" (MonadFn [g1|k18|] IO)
      :+: Name "k19" (MonadFn [g1|k19|] IO)
      :+: Name "k20" (MonadFn [g1|k20|] IO)
      :+: Name "k21" (MonadFn [g1|k21|] IO)
      :+: Name "k22" (MonadFn [g1|k22|] IO)
      :+: Name "k23" (MonadFn [g1|k23|] IO)
      :+: Name "k24" (MonadFn [g1|k24|] IO)
      :+: Name "k25" (MonadFn [g1|k25|] IO)
      :+: Name "k26" (MonadFn [g1|k26|] IO)
      :+: Name "k27" (MonadFn [g1|k27|] IO)
      :+: Name "k28" (MonadFn [g1|k28|] IO)
      :+: Name "k29" (MonadFn [g1|k29|] IO)
      :+: Name "k30" (MonadFn [g1|k30|] IO)
      :+: End

hardToCompileFn
  ∷ ∀ d d1
   . ( d1 ~ HardToCompileFnA d
     , ToConstraint (Follow (HardToCompileFnD d1))
     )
  ⇒ IO ()
hardToCompileFn = do
  False ← monadfn @[g1|k01|] 5
  False ← monadfn @[g1|k02|] 5
  False ← monadfn @[g1|k03|] 5
  False ← monadfn @[g1|k04|] 5
  False ← monadfn @[g1|k05|] 5
  False ← monadfn @[g1|k06|] 5
  False ← monadfn @[g1|k07|] 5
  False ← monadfn @[g1|k08|] 5
  False ← monadfn @[g1|k09|] 5
  False ← monadfn @[g1|k10|] 5
  False ← monadfn @[g1|k11|] 5
  False ← monadfn @[g1|k12|] 5
  False ← monadfn @[g1|k13|] 5
  False ← monadfn @[g1|k14|] 5
  False ← monadfn @[g1|k15|] 5
  False ← monadfn @[g1|k16|] 5
  False ← monadfn @[g1|k17|] 5
  False ← monadfn @[g1|k18|] 5
  False ← monadfn @[g1|k19|] 5
  False ← monadfn @[g1|k20|] 5
  False ← monadfn @[g1|k21|] 5
  False ← monadfn @[g1|k22|] 5
  False ← monadfn @[g1|k23|] 5
  False ← monadfn @[g1|k24|] 5
  False ← monadfn @[g1|k25|] 5
  False ← monadfn @[g1|k26|] 5
  False ← monadfn @[g1|k27|] 5
  False ← monadfn @[g1|k28|] 5
  False ← monadfn @[g1|k29|] 5
  False ← monadfn @[g1|k30|] 5
  return ()
