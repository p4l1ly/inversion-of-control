{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ConstraintKinds #-}
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
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file -ddump-file-prefix=/tmp/foo #-}

module Main where

import Data.Traversable
import Data.Semigroup
import GHC.TypeLits (Symbol)
import Control.Monad.Reader
import Data.IORef
import Data.Functor.Compose
import Data.Fix hiding (cata)
import Control.Monad.Free
import qualified InversionOfControl.Recursion.IORefGraph as RecDag
import qualified InversionOfControl.Recursion.Free as RecFree
import qualified InversionOfControl.Recursion.Fix as RecFix
import qualified InversionOfControl.Recursion.Pure as RecPure
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.GMonadTrans
import Data.Kind
import Data.Functor.Classes

data BoolFormula int bool =
  And bool bool
  | Not bool
  | Leq int int
  | BoolLit Bool
  deriving (Eq, Functor, Foldable, Traversable)

instance Show int => Show1 (BoolFormula int) where
  liftShowsPrec sp _ d = \case
    And a b -> showsBinaryWith sp sp "And" d a b
    Not a -> showsUnaryWith sp "Not" d a
    Leq a b -> showsBinaryWith showsPrec showsPrec "Leq" d a b
    BoolLit b -> showsUnaryWith showsPrec "BoolLit" d b

instance (Show int, Show bool) => Show (BoolFormula int bool) where
  show (And a b) = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Leq a b) = "(" ++ show a ++ " <= " ++ show b ++ ")"
  show (Not a) = "!" ++ show a
  show (BoolLit False) = "F"
  show (BoolLit True) = "T"

data IntFormula bool int =
  Count [bool]
  | Plus int int
  | IntLit Int
  deriving (Eq, Functor, Foldable, Traversable)

instance Show bool => Show1 (IntFormula bool) where
  liftShowsPrec sp s1 d = \case
    Count xs -> showsUnaryWith showsPrec "Count" d xs
    Plus a b -> showsBinaryWith sp sp "Plus" d a b
    IntLit i -> showsUnaryWith showsPrec "IntLit" d i

instance (Show int, Show bool) => Show (IntFormula int bool) where
  show (Count xs) = show xs
  show (Plus a b) = "(" ++ show a ++ " + " ++ show b ++ ")"
  show (IntLit i) = show i

fix1_val :: Bool -> Fix (BoolFormula Int)
fix1_val val = Fix $ And
  (Fix $ Not $ Fix $ And leq (Fix $ BoolLit val))
  (Fix $ And leq (Fix $ Not $ Fix $ BoolLit val))
  where leq = (Fix $ Leq 1 2)

fterm x = Right (Fix (Compose x))

fix1_var :: Fix (Compose (BoolFormula Int) (Either Word))
fix1_var = Fix $ Compose $ And
  (fterm $ Not $ fterm $ And leq (Left 0))
  (fterm $ And leq (fterm $ Not $ Left 0))
  where leq = (fterm $ Leq 1 2)

-- Free is just the same as Fix+Compose+Either (even in memory, as Fix and Compose are newtypes)
free1 :: Free (BoolFormula Int) Word
free1 = Free $ And
  (Free $ Not $ Free $ And leq (Pure 0))
  (Free $ And leq (Free $ Not $ Pure 0))
  where leq = (Free $ Leq 1 2)

term x = Right (Free (Compose x))
shared x = Right (Pure x)

iorefg1_val :: Bool -> IO (RecDag.RefFix (BoolFormula Int))
iorefg1_val val = do
  leq <- RecDag.buildFoldable $ Leq 1 2
  RecDag.buildFree $ Free $ And
    (Free $ Not $ Free $ And (Pure leq) (Free $ BoolLit val))
    (Free $ And (Pure leq) (Free $ Not $ Free $ BoolLit val))

iorefg1_var :: IO (RecDag.RefFix (Compose (BoolFormula Int) (Either Word)))
iorefg1_var = do
  leq <- RecDag.buildFoldable $ Compose $ Leq 1 2
  RecDag.buildFree $ Free $ Compose $ And
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

-- boolShareCount
--   :: forall d m bool self.
--   ( Int ~ [f|bx|]
--   , Sum Int ~ [f|p|]
--   , [f|r|] ~ RecDag.RefFix [fk|f|]
--   , Monad [fk|m|]
--   ) => Sum Int
--   -> self
--   -> BoolFormula bool [f|r|]
--   -> RecDag.SemigroupA (RecDag.RecFixD d) Int
-- boolShareCount (Sum p) _ fr = RecDag.SemigroupA $ Compose do
--   let RecDag.SemigroupA (Compose bef) =
--         for fr \(RecDag.RefFix child) -> RecDag.SemigroupA $ Compose do
--           recur <- ask
--           let RecDag.SemigroupA (Compose bef) = recur (Sum 1) child
--           bef
--   aft <- bef
--   return do (fromEnum (p > 1) +) . sum <$> aft

type RunCIO d m a = E [k|runCIO|] (CIO a -> m a)
type GoBool d m = E [k|goBool|] ([f|bool|] -> m Bool)
type GoInt d m = E [k|goInt|] ([f|int|] -> m Int)

type RecAppBase d m =
  ( Monad m
  , forall a. KFn (RunCIO d m a)
  , Show [f|bool|]
  , Show [f|int|]
  ) :: Constraint

type RecAppAlg d m =
  ( RecAppBase d m
  , KFn (GoBool d m)
  , KFn (GoInt d m)
  ) :: Constraint

intAlgebra :: forall d m. RecAppAlg d m => IntFormula [f|bool|] [f|int|] -> m Int
intAlgebra = \case
  Count xs -> do
    kfn @(RunCIO d _ _) incCounter
    args <- mapM (kfn @(GoBool d m)) xs
    let result = sum $ map fromEnum args
    kfn @(RunCIO d _ _) $ lift do print ("[]", result, args, xs)
    return result
  Plus x y -> do
    args <- (,) <$> kfn @(GoInt d m) x <*> kfn @(GoInt d m) y
    let result = uncurry (+) args
    kfn @(RunCIO d _ _) $ lift do print ("++", result, args, x, y)
    return result
  IntLit i -> do
    kfn @(RunCIO d _ _) $ lift do print ("II", i)
    return i

boolAlgebra :: forall d m. (RecAppAlg d m) => BoolFormula [f|int|] [f|bool|] -> m Bool
boolAlgebra = \case
  And x y -> do
    args <- (,) <$> kfn @(GoBool d m) x <*> kfn @(GoBool d m) y
    let result = uncurry (&&) args
    kfn @(RunCIO d _ _) $ lift do print ("&&", result, args, x, y)
    return result
  Not x -> do
    args <- kfn @(GoBool d m) x
    let result = not args
    kfn @(RunCIO d _ _) $ lift do print ("!!", result, args, x)
    return result
  Leq x y -> do
    kfn @(RunCIO d _ _) incCounter
    args <- (,) <$> kfn @(GoInt d m) x <*> kfn @(GoInt d m) y
    let result = uncurry (<=) args
    kfn @(RunCIO d _ _) $ lift do print ("<=", result, args, x, y)
    return result
  BoolLit b -> do
    kfn @(RunCIO d _ _) $ lift do print ("BB", b)
    return b

-- Basic recursion

type RecApp d m =
  ( RecAppBase d m
  , KFn (RecBool d m)
  , KFn (RecInt d m)
  ) :: Constraint

type RecBool d m = [e|CataE|recBool|] [f|bool|] (BoolFormula [f|int|] [f|bool|]) (m Bool)
type RecInt d m = [e|CataE|recInt|] [f|int|] (IntFormula [f|bool|] [f|int|]) (m Int)

data GoBool1 d
data GoInt1 d

instance (RecApp d m, bool ~ [f|bool|]) => KFn (E (K Zero (GoBool1 d)) (bool -> m Bool))
  where kfn = recBool @d

instance (RecApp d m, int ~ [f|int|]) => KFn (E (K Zero (GoInt1 d)) (int -> m Int))
  where kfn = recInt @d

data RecD d
type instance Definition (RecD d) =
  Name "goBool" (GoBool1 d)
  :+: Name "goInt" (GoInt1 d)
  :+: Follow d

recBool :: forall d m. RecApp d m => [f|bool|] -> m Bool
recBool = cata @(RecBool d m) (boolAlgebra @(RecD d))

recInt :: forall d m. RecApp d m => [f|int|] -> m Int
recInt = cata @(RecInt d m) (intAlgebra @(RecD d))

-- Valuated var recursion

type VarT = ReaderT (Word -> Bool)
type instance Unlift (ReaderT _ m) = m

type RecAppVar d m =
  ( Monad m
  , RecAppBase (VarD d) (VarT m)
  , KFn (RecBoolVar d m)
  , KFn (RecInt (VarD d) (VarT m))
  ) :: Constraint

type RecBoolVar d m = [e|CataE|recBool|] [f|bool|]
  (Compose (BoolFormula [f|int|]) (Either Word) [f|bool|]) (VarT m Bool)

data GoBool2 d
data GoInt2 d

instance (RecAppVar d m, bool ~ [f|bool|]) =>
  KFn (E (K Zero (GoBool2 d)) (Either Word bool -> VarT m Bool))
  where kfn = recBoolVar @d

instance (RecAppVar d m, int ~ [f|int|]) => KFn (E (K Zero (GoInt2 d)) (int -> VarT m Int))
  where kfn = recIntVar @d

recBoolVar :: forall d m. RecAppVar d m => Either Word [f|bool|] -> VarT m Bool
recBoolVar = \case
  Left x -> ($ x) <$> ask
  Right r -> cata @(RecBoolVar d m) (boolAlgebra @(VarD d) . getCompose) r

recIntVar :: forall d m. RecAppVar d m => [f|int|] -> VarT m Int
recIntVar = cata @(RecInt (VarD d) (VarT m)) $ intAlgebra @(VarD d)

data VarD d
type instance Definition (VarD d) =
  Name "bool" (Either Word [f|bool|])
  :+: Name "goBool" (GoBool2 d)
  :+: Name "goInt" (GoInt2 d)
  :+: Follow d

type ValuateE key p r a b v m  = E (K Zero (Valuate key))
  ((p -> r -> a -> ReaderT (v -> b) m b) -> p -> Either v r -> ReaderT (v -> b) m b)

data Valuate key
instance
  (Monad m, KFn (E key (Recur p r a (ReaderT (v -> b) m b)))) =>
  KFn (ValuateE key p r a b v m)
  where
  kfn algebra p er = case er of
    Left x -> ($ x) <$> ask
    Right r -> kfn @(E key (Recur p r a (ReaderT (v -> b) m b))) algebra p r

data D0
type instance Definition D0 =
  Name "runCIO" Lifter
  :+: Name "recBool" RecPure.Rec
  :+: Name "recInt" RecPure.Rec
  :+: Name "goBool" RecPure.Go
  :+: Name "goInt" RecPure.Go
  :+: Name "bool" Bool
  :+: Name "int" Int
  :+: End

data FixD
type instance Definition FixD =
  Name "recBool" RecFix.Rec
  :+: Name "bool" (Fix (BoolFormula Int))
  :+: Follow D0

data VarFixD
type instance Definition VarFixD =
  Name "bool" (Fix (Compose (BoolFormula Int) (Either Word)))
  :+: Follow FixD

data FreeD
type instance Definition FreeD =
  Name "recBool" RecFree.Rec
  :+: Name "bool" (Free (BoolFormula Int) Bool)
  :+: Follow D0

data DagD
type instance Definition DagD =
  Name "recBool" (RecDag.RecFix (Succ Zero))
  :+: Name "bool" (RecDag.RefFix (BoolFormula Int))
  :+: Name "lift" ()
  :+: Follow D0

data VarDagD
type instance Definition VarDagD =
  Name "bool" (RecDag.RefFix (Compose (BoolFormula Int) (Either Word)))
  :+: Follow DagD

-- data SemigroupE
-- type instance Definition SemigroupE =
--   Name "p" (Sum Int)
--   :+: Name "f" (Kindy (BoolFormula Int))
--   :+: Name "r" (RecDag.RefFix (BoolFormula Int))
--   :+: Name "a" (BoolFormula Int [gs|r|])
--   :+: Name "m" (Kindy IO)
--   :+: Name "bx" Int
--   :+: Name "b" (RecDag.SemigroupA (RecDag.RecFixD SemigroupE) [gs|bx|])
--   :+: Name "c" (Kindy (RecDag.SemigroupA (RecDag.RecFixD SemigroupE)))
--   :+: End

newtype BoolIntFormula = BoolIntFormula (BoolFormula IntBoolFormula BoolIntFormula)
  deriving newtype Show
newtype IntBoolFormula = IntBoolFormula (IntFormula BoolIntFormula IntBoolFormula)
  deriving newtype Show

data RecIntBool
instance KFn (RecurE n RecIntBool p IntBoolFormula (IntFormula BoolIntFormula IntBoolFormula) b)
  where kfn algebra p r@(IntBoolFormula fr) = algebra p r fr

data RecBoolInt
instance KFn (RecurE n RecBoolInt p BoolIntFormula (BoolFormula IntBoolFormula BoolIntFormula) b)
  where kfn algebra p r@(BoolIntFormula fr) = algebra p r fr

data BoolIntD
type instance Definition BoolIntD =
  Name "recBool" RecBoolInt
  :+: Name "recInt" RecIntBool
  :+: Name "bool" BoolIntFormula
  :+: Name "int" IntBoolFormula
  :+: Follow D0

type BoolIntFormula'Body = (BoolFormula (RecDag.Ref IntBoolFormula') (RecDag.Ref BoolIntFormula'))
type IntBoolFormula'Body = (IntFormula (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula'))
newtype BoolIntFormula' = BoolIntFormula' BoolIntFormula'Body
newtype IntBoolFormula' = IntBoolFormula' IntBoolFormula'Body

data RecBoolInt' n0
instance
  KFn (RecurE nb (RecDag.Rec n0) p (RecDag.Ref BoolIntFormula') BoolIntFormula' (mb xb))
  => KFn (RecurE nb (RecBoolInt' n0) p (RecDag.Ref BoolIntFormula') BoolIntFormula'Body (mb xb))
  where
  kfn algebra p r =
    kfn @(RecurE nb (RecDag.Rec n0) p (RecDag.Ref BoolIntFormula') BoolIntFormula' (mb xb))
      (\p r (BoolIntFormula' fr) -> algebra p r fr) p r

data RecIntBool' n0
instance
  KFn (RecurE nb (RecDag.Rec n0) p (RecDag.Ref IntBoolFormula') IntBoolFormula' (mb xb))
  => KFn (RecurE nb (RecIntBool' n0) p (RecDag.Ref IntBoolFormula') IntBoolFormula'Body (mb xb))
  where
  kfn algebra p r =
    kfn @(RecurE nb (RecDag.Rec n0) p (RecDag.Ref IntBoolFormula') IntBoolFormula' (mb xb))
      (\p r (IntBoolFormula' fr) -> algebra p r fr) p r

data BoolIntD'
type instance Definition BoolIntD' =
  Name "recBool" (RecBoolInt' (Succ (Succ Zero)))
  :+: Name "lift" ()
  :+: Name "recInt" (RecIntBool' (Succ Zero))
  :+: Name "bool" (RecDag.Ref BoolIntFormula')
  :+: Name "int" (RecDag.Ref IntBoolFormula')
  :+: Name "lift" ()
  :+: Follow D0

-- data RecBoolInt'D d
-- type instance Definition (RecBoolInt'D d) = Name "a" BoolIntFormula' :+: Follow d
-- 
-- data RecIntBool' n
-- instance
--   ( Monad [fk|m|]
--   , [f|r|] ~ RecDag.Ref IntBoolFormula'
--   , [f|a|] ~ IntFormula (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula')
--   , Recur (K n (RecDag.Rec n')) (RecIntBool'D d)
--   ) =>
--   Recur (K n (RecIntBool' n')) d
--   where
--   recur algebra act =
--     recur @(K n (RecDag.Rec n')) @(RecIntBool'D d)
--       (\p r (IntBoolFormula' fr) -> algebra p r fr)
--       act
-- 
-- data RecIntBool'D d
-- type instance Definition (RecIntBool'D d) = Name "a" IntBoolFormula' :+: Follow d
-- 
-- type RecM2In1 r1 r2 b1 b2 = ReaderT (() -> r1 -> RecM2 r1 r2 b1 b2 b1) CIO
-- type RecM2In2 r1 r2 b1 b2 = ReaderT (() -> r2 -> RecM2 r1 r2 b1 b2 b2) (RecM2In1 r1 r2 b1 b2)
-- 
-- newtype RecM2 r1 r2 b1 b2 c = RecM2
--   {unRecM2 :: RecM2In2 r1 r2 b1 b2 c}
--   deriving newtype (Functor, Applicative, Monad)
-- 
-- instance GMonadTrans (RecM2 r1 r2 b1 b2) (RecM2In2 r1 r2 b1 b2) where
--   glift = RecM2
-- 
-- data BoolIntE
-- type instance Definition BoolIntE =
--   Name "p" ()
--   :+: Name "r" BoolIntFormula
--   :+: Name "a" (BoolFormula IntBoolFormula BoolIntFormula)
--   :+: Name "m" (Kindy CIO)
--   :+: Name "bx" Bool
--   :+: Name "bm" (Kindy (RecM2 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In1 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- data IntBoolE
-- type instance Definition IntBoolE =
--   Name "p" ()
--   :+: Name "r" IntBoolFormula
--   :+: Name "a" (IntFormula BoolIntFormula IntBoolFormula)
--   :+: Name "m" (Kindy (RecM2In1 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "bx" Int
--   :+: Name "bm" (Kindy (RecM2 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In2 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- data BoolInt'E
-- type instance Definition BoolInt'E =
--   Name "p" ()
--   :+: Name "r" (RecDag.Ref BoolIntFormula')
--   :+: Name "a" (BoolFormula (RecDag.Ref IntBoolFormula') (RecDag.Ref BoolIntFormula'))
--   :+: Name "m" (Kindy CIO)
--   :+: Name "bx" Bool
--   :+: Name "bm" (Kindy (RecM2 (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula') Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In1 (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula') Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- data IntBool'E
-- type instance Definition IntBool'E =
--   Name "p" ()
--   :+: Name "r" (RecDag.Ref IntBoolFormula')
--   :+: Name "a" (IntFormula (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula'))
--   :+: Name "m" (Kindy (RecM2In1 (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula') Bool Int))
--   :+: Name "bx" Int
--   :+: Name "bm" (Kindy (RecM2 (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula') Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In2 (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula') Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End

fix2 :: Bool -> Bool -> BoolIntFormula
fix2 val1 val2 = BoolIntFormula $ And
  (BoolIntFormula $ Not $ BoolIntFormula $ And leq (BoolIntFormula $ BoolLit val1))
  (BoolIntFormula $ And leq (BoolIntFormula $ Not $ BoolIntFormula $ BoolLit val1))
  where
    leq = BoolIntFormula $ Leq count2 (IntBoolFormula $ IntLit 2)
    count = IntBoolFormula $ Count [tv2, BoolIntFormula $ BoolLit True, tv2]
    count2 = IntBoolFormula $ Plus count count
    tv2 = BoolIntFormula $ And (BoolIntFormula $ BoolLit True) (BoolIntFormula $ BoolLit val2)

iorefg2 :: Bool -> Bool -> IO (RecDag.Ref BoolIntFormula')
iorefg2 val1 val2 = do
  v2 <- RecDag.buildTopo 0 $ BoolIntFormula' $ BoolLit val2
  print ("v2", v2)
  t <- RecDag.buildTopo 0 $ BoolIntFormula' $ BoolLit True
  print ("t", t)
  tv2 <- RecDag.buildTopo 1 $ BoolIntFormula' $ And t v2
  print ("tv2", tv2)
  count <- RecDag.buildTopo 2 $ IntBoolFormula' $ Count [tv2, t, tv2]
  print ("count", count)
  plus <- RecDag.buildTopo 3 $ IntBoolFormula' $ Plus count count
  print ("plus", plus)
  l1 <- RecDag.buildTopo 0 $ IntBoolFormula' $ IntLit 2
  print ("l1", l1)
  leq <- RecDag.buildTopo 3 $ BoolIntFormula' $ Leq plus l1
  print ("leq", leq)
  v1 <- RecDag.buildTopo 0 $ BoolIntFormula' $ BoolLit val1
  print ("v1", v1)
  nv1 <- RecDag.buildTopo 1 $ BoolIntFormula' $ Not v1
  print ("nv1", nv1)
  leqv1 <- RecDag.buildTopo 4 $ BoolIntFormula' $ And leq v1
  print ("leqv1", leqv1)
  leqnv1 <- RecDag.buildTopo 4 $ BoolIntFormula' $ And leq nv1
  print ("leqnv1", leqnv1)
  nleqv1 <- RecDag.buildTopo 5 $ BoolIntFormula' $ Not leqv1
  print ("nleqv1", nleqv1)
  RecDag.buildTopo 6 $ BoolIntFormula' $ And nleqv1 leqnv1

main ∷ IO ()
main = do
  -- Test the algebrae

  2 <- runCIO do
    False <- boolAlgebra @D0 $ And True False 
    True <- boolAlgebra @D0 $ Not False
    True <- boolAlgebra @D0 $ Leq 1 2
    False <- boolAlgebra @D0 $ BoolLit False
    3 <- intAlgebra @D0 $ Count [False, True, True, False, True]
    5 <- intAlgebra @D0 $ Plus 3 2
    9 <- intAlgebra @D0 $ IntLit 9
    return ()

  -- Test recursion of Fix

  2 <- runCIO do
    False <- recBool @FixD $ fix1_val True
    return ()

  2 <- runCIO do
    True <- recBool @FixD $ fix1_val False
    return ()

  2 <- runCIO do
    False <- runReaderT (recBoolVar @(LiftUp VarFixD) (Right fix1_var)) (\0 -> True)
    return ()

  2 <- runCIO do
    True <- runReaderT (recBoolVar @(LiftUp VarFixD) (Right fix1_var)) (\0 -> False)
    return ()

  -- Test recursion of Free

  2 <- runCIO do
    False <- recBool @FreeD $ fmap (\0 -> True) free1
    return ()

  2 <- runCIO do
    True <- recBool @FreeD $ fmap (\0 -> False) free1
    return ()

  -- Test recursion of IORefGraph

  iorefg1_True <- iorefg1_val True
  1 <- runCIO do
    RecDag.runRecT @(Succ Zero) do
      False <- recBool @DagD iorefg1_True
      return ()

  iorefg1_False <- iorefg1_val False
  1 <- runCIO do
    RecDag.runRecT @(Succ Zero) do
      True <- recBool @DagD iorefg1_False
      return ()

  iorefg1_var' <- iorefg1_var
  1 <- runCIO do
    RecDag.runRecT @(Succ Zero) do
      False <- runReaderT (recBoolVar @(LiftUp VarDagD) (Right iorefg1_var')) (\0 -> True)
      return ()

  1 <- runCIO do
    RecDag.runRecT @(Succ Zero) do
      True <- runReaderT (recBoolVar @(LiftUp VarDagD) (Right iorefg1_var')) (\0 -> False)
      return ()

  -- Test mutual recursion of "Fix"

  6 <- runCIO do
    True <- recBool @BoolIntD $ fix2 False False
    return ()

  6 <- runCIO do
    False <- recBool @BoolIntD $ fix2 True False
    return ()

  6 <- runCIO do
    False <- recBool @BoolIntD $ fix2 False True
    return ()

  -- Test mutual recursion of IORefGraph

  iorefg2_00 <- iorefg2 False False
  2 <- runCIO do
    RecDag.runRecT @(Succ Zero) do
      RecDag.runRecT @(Succ (Succ Zero)) do
        True <- recBool @BoolIntD' iorefg2_00
          :: RecDag.RecT () BoolIntFormula' Bool
              (RecDag.RecT () IntBoolFormula' Int CIO) Bool
        return ()

  -- 2 <- runCIO do
  --   True <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
  --     (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --       cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
  --         (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_00)
  --   return ()

  -- iorefg2_10 <- iorefg2 True False
  -- 2 <- runCIO do
  --   False <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
  --     (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --       cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
  --         (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_10)
  --   return ()

  -- iorefg2_01 <- iorefg2 False True
  -- 2 <- runCIO do
  --   False <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
  --     (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --       cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
  --         (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_01)
  --   return ()

  -- -- Test two-way recursion (the mutual one is unsupported)
  -- 2 <- recur @(K Zero RecDag.SemigroupRecFix) @SemigroupE
  --   (boolShareCount @SemigroupE)
  --   $ RecDag.SemigroupA $ Compose do
  --     recur <- ask
  --     let RecDag.RefFix r = iorefg1_True
  --     let RecDag.SemigroupA (Compose bef) = recur (Sum 1) r
  --     bef

  -- -- Test recursion of composition of IORefGraph and Free
  -- -- TODO

  -- -- Cleanup
  -- -- TODO

  return ()
