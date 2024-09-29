{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import GHC.TypeLits (Symbol)
import Control.Monad.Reader
import Data.IORef
import Data.Functor.Compose
import Data.Fix hiding (cata)
import Control.Monad.Free
import qualified InversionOfControl.Recursion.IORefGraph as RecIO
import qualified InversionOfControl.Recursion.Free as RecFree
import qualified InversionOfControl.Recursion.Fix as RecFix
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.GMonadTrans
import Data.Kind

data BoolFormula int bool =
  And bool bool
  | Not bool
  | Leq int int
  | BoolLit Bool
  deriving (Show, Eq, Functor, Foldable, Traversable)

data IntFormula bool int =
  Count [bool]
  | Plus int int
  | IntLit Int
  deriving (Show, Eq, Functor, Foldable, Traversable)

fix1_val :: Bool -> Fix (BoolFormula Int)
fix1_val val = Fix $ And
  (Fix $ Not $ Fix $ And (Fix $ Leq 1 2) (Fix $ BoolLit val))
  (Fix $ And (Fix $ Leq 1 2) (Fix $ Not $ Fix $ BoolLit val))

fterm x = Right (Fix (Compose x))

fix1_var :: Fix (Compose (BoolFormula Int) (Either Word))
fix1_var = Fix $ Compose $ And
  (fterm $ Not $ fterm $ And (fterm $ Leq 1 2) (Left 0))
  (fterm $ And (fterm $ Leq 1 2) (fterm $ Not $ Left 0))

-- Free is just the same as Fix+Compose+Either (even in memory, as Fix and Compose are newtypes)
free1 :: Free (BoolFormula Int) Word
free1 = Free $ And
  (Free $ Not $ Free $ And (Free $ Leq 1 2) (Pure 0))
  (Free $ And (Free $ Leq 1 2) (Free $ Not $ Pure 0))

term x = Right (Free (Compose x))
shared x = Right (Pure x)

iorefg1_val :: Bool -> IO (RecIO.RefFix (BoolFormula Int))
iorefg1_val val = do
  leq <- RecIO.buildFoldable $ Leq 1 2
  RecIO.buildFree $ Free $ And
    (Free $ Not $ Free $ And (Pure leq) (Free $ BoolLit val))
    (Free $ And (Pure leq) (Free $ Not $ Free $ BoolLit val))

iorefg1_var :: IO (RecIO.RefFix (Compose (BoolFormula Int) (Either Word)))
iorefg1_var = do
  leq <- RecIO.buildFoldable $ Compose $ Leq 1 2
  RecIO.buildFree $ Free $ Compose $ And
    (term $ Not $ term $ And (shared leq) (Left 0))
    (term $ And (shared leq) (term $ Not $ Left 0))

type CIO = ReaderT (IORef Int) IO

incCounter :: CIO ()
incCounter = do
  ref <- ask
  liftIO $ modifyIORef' ref (+1)

runCIO :: CIO a -> IO Int
runCIO act = do
  ref <- newIORef 0
  runReaderT act ref
  readIORef ref

boolAlgebra ::
  forall d m.
  ( MonadFnN (RecBool d m [f|refBool|])
  , MonadFnN (RecInt d m [f|refInt|])
  , MonadFnN (RunCIO d m ())
  )
  => BoolFormula [f|refInt|] [f|refBool|]
  -> m Bool
boolAlgebra = \case
  And x y -> (&&) <$> getBool x <*> getBool y
  Not x -> not <$> getBool x
  Leq x y -> do
    monadfnn @(RunCIO d _ _) incCounter
    (<=) <$> getInt x <*> getInt y
  BoolLit b -> return b
  where
    getBool = cataRec @(RecBool d _ _)
    getInt = cataRec @(RecInt d _ _)

boolAlgebraVar ::
  forall d m.
  ( MonadFnN (RecBool d m [f|refBool|])
  , MonadFnN (RecInt (VarD d) (ReaderT (Word -> Bool) m) [f|refInt|])
  , MonadFnN (RunCIO (VarD d) (ReaderT (Word -> Bool) m) ())
  )
  => (Word -> Bool)
  -> Compose (BoolFormula [f|refInt|]) (Either Word) [f|refBool|]
  -> m Bool
boolAlgebraVar valuation (Compose fr) = runReaderT (boolAlgebra @(VarD d) fr) valuation

data VarD d
type instance Definition (VarD d) =
  Name "refBool" (Either Word [f|refBool|])
  :+: Name "recBool" (Valuate [k|recBool|])
  :+: Follow (LiftUp d)

data Valuate key
instance
  ( Monad m
  , MonadFnN (E key (p, r) b m)
  )
  => MonadFn (E (K Zero (Valuate key)) (p, Either a r) b (ReaderT (a -> b) m))
  where
  monadfn (p, er) = case er of
    Left x -> ($ x) <$> ask
    Right r -> lift $ monadfnn @(E key (p, r) b m) (p, r)

instance
  (Monad m, MonadFn (E (K n (Valuate key)) a b m)) =>
  MonadFnN (E (K n (Valuate key)) a b m) where
  monadfnn = monadfn @(E (K n (Valuate key)) a b m)


data D0
type instance Definition D0 =
  Name "runCIO" Lifter
  :+: Name "recBool" (Pure Bool)
  :+: Name "recInt" (Pure Int)
  :+: Name "refBool" Bool
  :+: Name "refInt" Int
  :+: End

data D1 d
type instance Definition (D1 d) =
  Name "refBool" [g|r|]
  :+: Follow (LiftUp (RecurD "recBool" d D0))

data D1' d
type instance Definition (D1' d) =
  Name "refBool" [g|r|]
  :+: Follow (LiftUp (RecIO.FixRecurD "recBool" d D0))

type RecBool d m r = E [k|recBool|] ((), r) Bool m
type RecInt d m r = E [k|recInt|] ((), r) Int m
type RunCIO d m a = E [k|runCIO|] (CIO a) a m

data Lifter
instance Monad m => MonadFn (E (K Zero Lifter) (m a) a m) where
  monadfn act = act

instance
  (Monad m, MonadFn (E (K n Lifter) a b m)) =>
  MonadFnN (E (K n Lifter) a b m) where
  monadfnn = monadfn @(E (K n Lifter) a b m)

data Pure x
instance Monad m => MonadFnN (E (K n (Pure x)) ((), x) x m) where
  monadfnn (_, x) = pure x

newtype RecM r b c = RecM {unRecM :: ReaderT (() -> r -> RecM r b b) CIO c}
  deriving newtype (Functor, Applicative, Monad)

instance GMonadTrans (RecM r b) (ReaderT (() -> r -> RecM r b b) CIO) where
  glift = RecM

data GenFixE (f :: Type -> Type)
type instance Definition (GenFixE f) =
  Name "p" ()
  :+: Name "f" (Kindy f)
  :+: Name "r" (Fix f)
  :+: Name "a" (f [gs|r|])
  :+: Name "m" (Kindy CIO)
  :+: Name "c" (Kindy (ReaderT (() -> [gs|r|] -> RecM [gs|r|] Bool Bool) CIO))
  :+: Name "bm" (Kindy (RecM (Fix f) Bool))
  :+: Name "bx" Bool
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: End
type FixE = GenFixE (BoolFormula Int)
type VFixE = GenFixE (Compose (BoolFormula Int) (Either Word))

data GenGraphE (f :: Type -> Type)
type instance Definition (GenGraphE f) =
  Name "p" ()
  :+: Name "f" (Kindy f)
  :+: Name "r" (RecIO.RefFix f)
  :+: Name "a" (f [gs|r|])
  :+: Name "m" (Kindy CIO)
  :+: Name "c" (Kindy (ReaderT (() -> RecIO.Ref (f (RecIO.RefFix f)) -> RecM (RecIO.Ref (f (RecIO.RefFix f))) Bool Bool) CIO))
  :+: Name "bm" (Kindy (RecM (RecIO.Ref (f (RecIO.RefFix f))) Bool))
  :+: Name "bx" Bool
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: End
type GraphE = GenGraphE (BoolFormula Int)
type VGraphE = GenGraphE (Compose (BoolFormula Int) (Either Word))

data FreeE
type instance Definition FreeE =
  Name "p" ()
  :+: Name "f" (Kindy (BoolFormula Int))
  :+: Name "r" (Free [fsk|f|] Bool)
  :+: Name "a" ([fsk|f|] [gs|r|])
  :+: Name "m" (Kindy CIO)
  :+: Name "c" (Kindy (ReaderT (() -> [gs|r|] -> RecM [gs|r|] Bool Bool) CIO))
  :+: Name "bm" (Kindy (RecM [gs|r|] Bool))
  :+: Name "bx" Bool
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: End

newtype BoolIntFormula = BoolIntFormula (BoolFormula IntBoolFormula BoolIntFormula)
newtype IntBoolFormula = IntBoolFormula (IntFormula BoolIntFormula IntBoolFormula)

main ∷ IO ()
main = do
  1 <- runCIO do
    False <- boolAlgebra @D0 $ And True False 
    True <- boolAlgebra @D0 $ Not False
    True <- boolAlgebra @D0 $ Leq 1 2
    False <- boolAlgebra @D0 $ BoolLit False
    return ()

  2 <- runCIO do
    False <- cata @(K Zero RecFix.Rec) @FixE
      (boolAlgebra @(D1 FixE))
      (unRecM $ cataRec @(RecBool (D1 FixE) _ _) $ fix1_val True)
    return ()

  2 <- runCIO do
    True <- cata @(K Zero RecFix.Rec) @FixE
      (boolAlgebra @(D1 FixE))
      (unRecM $ cataRec @(RecBool (D1 FixE) _ _) $ fix1_val False)
    return ()

  2 <- runCIO do
    False <- cata @(K Zero RecFix.Rec) @VFixE
      (boolAlgebraVar @(D1 VFixE) (\0 -> True))
      (unRecM $ cataRec @(RecBool (D1 VFixE) _ _) $ fix1_var)
    return ()

  2 <- runCIO do
    True <- cata @(K Zero RecFix.Rec) @VFixE
      (boolAlgebraVar @(D1 VFixE) (\0 -> False))
      (unRecM $ cataRec @(RecBool (D1 VFixE) _ _) $ fix1_var)
    return ()

  2 <- runCIO do
    False <- cata @(K Zero RecFree.Rec) @FreeE
      (boolAlgebra @(D1 FreeE))
      (unRecM $ cataRec @(RecBool (D1 FreeE) _ _) $ fmap (\0 -> True) free1)
    return ()

  2 <- runCIO do
    True <- cata @(K Zero RecFree.Rec) @FreeE
      (boolAlgebra @(D1 FreeE))
      (unRecM $ cataRec @(RecBool (D1 FreeE) _ _) $ fmap (\0 -> False) free1)
    return ()

  iorefg1_True <- iorefg1_val True
  iorefg1_False <- iorefg1_val False
  iorefg1_var' <- iorefg1_var

  1 <- runCIO do
    False <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @GraphE
      (boolAlgebra @(D1' GraphE))
      (unRecM $ cataRec @(RecBool (D1' GraphE) _ _) $ iorefg1_True)
    return ()

  1 <- runCIO do
    True <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @GraphE
      (boolAlgebra @(D1' GraphE))
      (unRecM $ cataRec @(RecBool (D1' GraphE) _ _) $ iorefg1_False)
    return ()

  1 <- runCIO do
    False <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @VGraphE
      (boolAlgebraVar @(D1' VGraphE) (\0 -> True))
      (unRecM $ cataRec @(RecBool (D1' VGraphE) _ _) $ iorefg1_var')
    return ()

  1 <- runCIO do
    True <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @VGraphE
      (boolAlgebraVar @(D1' VGraphE) (\0 -> False))
      (unRecM $ cataRec @(RecBool (D1' VGraphE) _ _) $ iorefg1_var')
    return ()

  return ()
