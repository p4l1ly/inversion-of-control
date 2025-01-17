{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module InversionOfControl.MapRecur where

import Control.Monad.Trans
import InversionOfControl.Lift
import InversionOfControl.LiftN

data Explicit (k :: K) (r :: *) (r' :: *) (f :: *)
type family Er e :: * where
  Er (Explicit _ r _ _) = r
type family Er' e :: * where
  Er' (Explicit _ _ r' _) = r'
type family Ef e :: * where
  Ef (Explicit _ _ _ f) = f

type family Et (e :: *) :: (* -> *) -> * -> *

class (Monad m, MonadTrans (Et e), Monad (Et e m)) => Recur e m where
  runRecur :: Ef e -> ((Er e -> Et e m (Er' e)) -> Et e m a) -> m a
