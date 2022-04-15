{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module InversionOfControl.MonadFn where

import Control.Monad.Trans (MonadTrans (lift))
import InversionOfControl.Lift (K (K), Pean (Succ), Unwrap)

type family Param (k :: *) :: *
type family Result (k :: *) :: *

data Explicit (a :: *) (b :: *) (k :: *)
type instance Param (Explicit a _ _) = a
type instance Result (Explicit _ b _) = b

class Monad m => MonadFn (k :: K) (m :: * -> *) where
  monadfn :: Param (Unwrap k) -> m (Result (Unwrap k))

instance
  (MonadFn ( 'K n k) m, MonadTrans mt, Monad m, Monad (mt m)) =>
  MonadFn ( 'K (Succ n) k) (mt m)
  where
  monadfn p1 = lift (monadfn @( 'K n k) p1)

type MonadFn' k a b m = (MonadFn k m, b ~ Result (Unwrap k), a ~ Param (Unwrap k))
type Ask k a m = MonadFn' k () a m

ask :: forall k a m. (Ask k a m) => m a
ask = monadfn @k ()
