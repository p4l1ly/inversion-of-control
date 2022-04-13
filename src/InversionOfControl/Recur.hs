{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module InversionOfControl.Recur where

import InversionOfControl.Lift (K, Unwrap)

type family RecRef (k :: *) :: *
type family RecVal (k :: *) :: *
type family RecFun (k :: *) :: *

data RecK (r :: *) (r' :: *) (fun :: *) (k :: *)
type instance RecRef (RecK r _ _ _) = r
type instance RecVal (RecK _ r' _ _) = r'
type instance RecFun (RecK _ _ fun _) = fun

class Recur (k :: K) (m :: * -> *) where
  recur :: RecFun (Unwrap k) -> m (RecRef (Unwrap k) -> m (RecVal (Unwrap k)))
