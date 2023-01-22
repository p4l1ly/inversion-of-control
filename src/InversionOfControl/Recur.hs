{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module InversionOfControl.Recur where

import Control.Monad.Trans
import InversionOfControl.Lift
import InversionOfControl.LiftN

data Explicit (k :: K) (n' :: Pean) (r :: *) (fr :: *)
type family Ek e :: K where
  Ek (Explicit k _ _ _) = k
type family En' e :: Pean where
  En' (Explicit _ n' _ _) = n'
type family Er e :: * where
  Er (Explicit _ _ r _) = r
type family Efr e :: * where
  Efr (Explicit _ _ _ fr) = fr

type family Et (e :: *) :: (* -> *) -> * -> *

class (Monad m, MonadTrans (Et e), Monad (Et e m)) => Recur e b m where
  runRecur ::
    forall m' a.
    (Monad m', LiftN (En' e) (Et e m) m') =>
    ((Er e -> m' b) -> Efr e -> m' b) ->
    ((Er e -> m' b) -> Et e m a) ->
    m a
