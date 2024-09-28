{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module InversionOfControl.GMonadTrans where

import Control.Monad.Trans

class (Monad t, Monad m) => GMonadTrans t m | t -> m where
  glift :: m a -> t a

instance (Monad m, MonadTrans t) => GMonadTrans (t m) m where
  glift = lift
