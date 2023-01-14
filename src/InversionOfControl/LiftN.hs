{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module InversionOfControl.LiftN where

import Control.Monad.Trans (MonadTrans (lift))
import InversionOfControl.Lift (Pean (Succ))

class LiftN (n :: Pean) (m :: * -> *) (m' :: * -> *) where
  liftn :: m a -> m' a

instance (LiftN n m m', MonadTrans mt, Monad m') => LiftN (Succ n) m (mt m') where
  liftn (ma :: m a) = lift (liftn @n @m @m' ma :: m' a)

instance LiftN n m m where
  liftn = id
