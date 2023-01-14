{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
-- debug
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
-- {-# OPTIONS_GHC -fplugin-opt InversionOfControl.TcPlugin:no_getK_singletonDataCon #-}

module Main where

import InversionOfControl.Lift (K (K), Inherit, Pean (Zero))
import InversionOfControl.MonadFn (Explicit, MonadFn (monadfn), MonadFn0(monadfn0))
import InversionOfControl.TypeDict
  (Named (Name), ToConstraint, TypeDict (End, (:+:)), Definition, g, g1, Follow, Get)

data Even
data Odd

instance MonadFn0 (Explicit Int Bool Even) IO where
  monadfn0 = return . even

instance MonadFn0 (Explicit Int Bool Odd) IO where
  monadfn0 = return . odd

data OptionsD (lifts :: Pean)

type instance Definition (OptionsD lifts) =
      Name "k01" ('K lifts Even)
  :+: Name "k02" ('K lifts Even)
  :+: Name "k03" ('K lifts Even)
  :+: Name "k04" ('K lifts Even)
  :+: Name "k05" ('K lifts Even)
  :+: Name "k06" ('K lifts Even)
  :+: Name "k07" ('K lifts Even)
  :+: Name "k08" ('K lifts Even)
  :+: Name "k09" ('K lifts Even)
  :+: Name "k10" ('K lifts Even)
  :+: Name "k11" ('K lifts Even)
  :+: Name "k12" ('K lifts Even)
  :+: Name "k13" ('K lifts Even)
  :+: Name "k14" ('K lifts Even)
  :+: Name "k15" ('K lifts Even)
  :+: Name "k16" ('K lifts Even)
  :+: Name "k17" ('K lifts Even)
  :+: Name "k18" ('K lifts Even)
  :+: Name "k19" ('K lifts Even)
  :+: Name "k20" ('K lifts Even)
  :+: Name "k21" ('K lifts Even)
  :+: Name "k22" ('K lifts Even)
  :+: Name "k23" ('K lifts Even)
  :+: Name "k24" ('K lifts Even)
  :+: Name "k25" ('K lifts Even)
  :+: Name "k26" ('K lifts Even)
  :+: Name "k27" ('K lifts Even)
  :+: Name "k28" ('K lifts Even)
  :+: Name "k29" ('K lifts Even)
  :+: Name "k30" ('K lifts Even)
  :+: End

main :: IO ()
main = hardToCompileFn @OptionsD

data HardToCompileFnA (d :: *)
type instance Definition (HardToCompileFnA d) =
      Name "k01" (Inherit (Explicit Int Bool) [g|k01|])
  :+: Name "k02" (Inherit (Explicit Int Bool) [g|k02|])
  :+: Name "k03" (Inherit (Explicit Int Bool) [g|k03|])
  :+: Name "k04" (Inherit (Explicit Int Bool) [g|k04|])
  :+: Name "k05" (Inherit (Explicit Int Bool) [g|k05|])
  :+: Name "k06" (Inherit (Explicit Int Bool) [g|k06|])
  :+: Name "k07" (Inherit (Explicit Int Bool) [g|k07|])
  :+: Name "k08" (Inherit (Explicit Int Bool) [g|k08|])
  :+: Name "k09" (Inherit (Explicit Int Bool) [g|k09|])
  :+: Name "k10" (Inherit (Explicit Int Bool) [g|k10|])
  :+: Name "k11" (Inherit (Explicit Int Bool) [g|k11|])
  :+: Name "k12" (Inherit (Explicit Int Bool) [g|k12|])
  :+: Name "k13" (Inherit (Explicit Int Bool) [g|k13|])
  :+: Name "k14" (Inherit (Explicit Int Bool) [g|k14|])
  :+: Name "k15" (Inherit (Explicit Int Bool) [g|k15|])
  :+: Name "k16" (Inherit (Explicit Int Bool) [g|k16|])
  :+: Name "k17" (Inherit (Explicit Int Bool) [g|k17|])
  :+: Name "k18" (Inherit (Explicit Int Bool) [g|k18|])
  :+: Name "k19" (Inherit (Explicit Int Bool) [g|k19|])
  :+: Name "k20" (Inherit (Explicit Int Bool) [g|k20|])
  :+: Name "k21" (Inherit (Explicit Int Bool) [g|k21|])
  :+: Name "k22" (Inherit (Explicit Int Bool) [g|k22|])
  :+: Name "k23" (Inherit (Explicit Int Bool) [g|k23|])
  :+: Name "k24" (Inherit (Explicit Int Bool) [g|k24|])
  :+: Name "k25" (Inherit (Explicit Int Bool) [g|k25|])
  :+: Name "k26" (Inherit (Explicit Int Bool) [g|k26|])
  :+: Name "k27" (Inherit (Explicit Int Bool) [g|k27|])
  :+: Name "k28" (Inherit (Explicit Int Bool) [g|k28|])
  :+: Name "k29" (Inherit (Explicit Int Bool) [g|k29|])
  :+: Name "k30" (Inherit (Explicit Int Bool) [g|k30|])
  :+: End

data HardToCompileFnD (d1 :: *)
type instance Definition (HardToCompileFnD d1) =
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

hardToCompileFn ::
  forall d d1.
  ( d1 ~ HardToCompileFnA (d Zero)
  , ToConstraint (Follow (HardToCompileFnD d1))
  ) =>
  IO ()
hardToCompileFn = do
  False <- monadfn @[g1|k01|] 5
  False <- monadfn @[g1|k02|] 5
  False <- monadfn @[g1|k03|] 5
  False <- monadfn @[g1|k04|] 5
  False <- monadfn @[g1|k05|] 5
  False <- monadfn @[g1|k06|] 5
  False <- monadfn @[g1|k07|] 5
  False <- monadfn @[g1|k08|] 5
  False <- monadfn @[g1|k09|] 5
  False <- monadfn @[g1|k10|] 5
  False <- monadfn @[g1|k11|] 5
  False <- monadfn @[g1|k12|] 5
  False <- monadfn @[g1|k13|] 5
  False <- monadfn @[g1|k14|] 5
  False <- monadfn @[g1|k15|] 5
  False <- monadfn @[g1|k16|] 5
  False <- monadfn @[g1|k17|] 5
  False <- monadfn @[g1|k18|] 5
  False <- monadfn @[g1|k19|] 5
  False <- monadfn @[g1|k20|] 5
  False <- monadfn @[g1|k21|] 5
  False <- monadfn @[g1|k22|] 5
  False <- monadfn @[g1|k23|] 5
  False <- monadfn @[g1|k24|] 5
  False <- monadfn @[g1|k25|] 5
  False <- monadfn @[g1|k26|] 5
  False <- monadfn @[g1|k27|] 5
  False <- monadfn @[g1|k28|] 5
  False <- monadfn @[g1|k29|] 5
  False <- monadfn @[g1|k30|] 5
  return ()
