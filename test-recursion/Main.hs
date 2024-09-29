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
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
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

intAlgebra ::
  forall d m.
  ( MonadFnN (RecBool d m [f|refBool|])
  , MonadFnN (RecInt d m [f|refInt|])
  , MonadFnN (RunCIO d m ())
  , Show [f|refBool|]
  , Show [f|refInt|]
  )
  => IntFormula [f|refBool|] [f|refInt|]
  -> m Int
intAlgebra = \case
  Count xs -> do
    monadfnn @(RunCIO d _ _) incCounter
    args <- mapM getBool xs
    let result = sum $ map fromEnum args
    monadfnn @(RunCIO d _ _) $ lift do
      print ("[]", result, args, xs)
    return result
  Plus x y -> do
    args <- (,) <$> getInt x <*> getInt y
    let result = uncurry (+) args
    monadfnn @(RunCIO d _ _) $ lift do
      print ("++", result, args, x, y)
    return result
  IntLit i -> do
    monadfnn @(RunCIO d _ _) $ lift do
      print ("II", i)
    return i
  where
    getBool = cataRec @(RecBool d _ _)
    getInt = cataRec @(RecInt d _ _)

boolAlgebra ::
  forall d m.
  ( MonadFnN (RecBool d m [f|refBool|])
  , MonadFnN (RecInt d m [f|refInt|])
  , MonadFnN (RunCIO d m ())
  , Show [f|refBool|]
  , Show [f|refInt|]
  )
  => BoolFormula [f|refInt|] [f|refBool|]
  -> m Bool
boolAlgebra = \case
  And x y -> do
    args <- (,) <$> getBool x <*> getBool y
    let result = uncurry (&&) args
    monadfnn @(RunCIO d _ _) $ lift do
      print ("&&", result, args, x, y)
    return result
  Not x -> do
    args <- getBool x
    let result = not args
    monadfnn @(RunCIO d _ _) $ lift do
      print ("!!", result, args, x)
    return result
  Leq x y -> do
    monadfnn @(RunCIO d _ _) incCounter
    args <- (,) <$> getInt x <*> getInt y
    let result = uncurry (<=) args
    monadfnn @(RunCIO d _ _) $ lift do
      print ("<=", result, args, x, y)
    return result
  BoolLit b -> do
    monadfnn @(RunCIO d _ _) $ lift do
      print ("BB", b)
    return b
  where
    getBool = cataRec @(RecBool d _ _)
    getInt = cataRec @(RecInt d _ _)

boolAlgebraVar ::
  forall d m.
  ( MonadFnN (RecBool d m [f|refBool|])
  , MonadFnN (RecInt (VarD d) (ReaderT (Word -> Bool) m) [f|refInt|])
  , MonadFnN (RunCIO (VarD d) (ReaderT (Word -> Bool) m) ())
  , Show [f|refBool|]
  , Show [f|refInt|]
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

data D1_ d
type instance Definition (D1_ d) =
  Name "refBool" [g|r|]
  :+: Follow ([fk|recurd|] "recBool" d D0)

data D1 d
type instance Definition (D1 d) = Follow (LiftUp (D1_ d))

data D2_ d d1
type instance Definition (D2_ d d1) =
  Name "refInt" [g|r|]
  :+: Follow ([fk|recurd|] "recInt" d d1)

data D2 d d1
type instance Definition (D2 d d1) = Follow (LiftUp (D2_ d (D1_ d1)))

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
  :+: Name "bm" (Kindy (RecM [gs|r|] Bool))
  :+: Name "bx" Bool
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: Name "recurd" (Kindy RecurD)
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
  :+: Name "recurd" (Kindy RecIO.FixRecurD)
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
  :+: Name "recurd" (Kindy RecurD)
  :+: End

newtype BoolIntFormula = BoolIntFormula (BoolFormula IntBoolFormula BoolIntFormula)
  deriving newtype Show
newtype IntBoolFormula = IntBoolFormula (IntFormula BoolIntFormula IntBoolFormula)
  deriving newtype Show

data RecBoolInt
instance
  ( Monad [fk|m|]
  , [f|r|] ~ BoolIntFormula
  , [f|a|] ~ BoolFormula IntBoolFormula BoolIntFormula
  , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
  ) ⇒
  Recur (K n RecBoolInt) d
  where
  recur algebra act = do
    let rec p r@(BoolIntFormula fr) = algebra p r fr
    runReaderT act rec

data RecIntBool
instance
  ( Monad [fk|m|]
  , [f|r|] ~ IntBoolFormula
  , [f|a|] ~ IntFormula BoolIntFormula IntBoolFormula
  , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
  ) ⇒
  Recur (K n RecIntBool) d
  where
  recur algebra act = do
    let rec p r@(IntBoolFormula fr) = algebra p r fr
    runReaderT act rec

newtype BoolIntFormula' = BoolIntFormula' (BoolFormula (RecIO.Ref IntBoolFormula') (RecIO.Ref BoolIntFormula'))
newtype IntBoolFormula' = IntBoolFormula' (IntFormula (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula'))

data RecBoolInt' n
instance
  ( Monad [fk|m|]
  , [f|r|] ~ RecIO.Ref BoolIntFormula'
  , [f|a|] ~ BoolFormula (RecIO.Ref IntBoolFormula') (RecIO.Ref BoolIntFormula')
  , Recur (K n (RecIO.Rec n')) (RecBoolInt'D d)
  ) =>
  Recur (K n (RecBoolInt' n')) d
  where
  recur algebra act =
    recur @(K n (RecIO.Rec n')) @(RecBoolInt'D d)
      (\p r (BoolIntFormula' fr) -> algebra p r fr)
      act

data RecBoolInt'D d
type instance Definition (RecBoolInt'D d) = Name "a" BoolIntFormula' :+: Follow d

data RecIntBool' n
instance
  ( Monad [fk|m|]
  , [f|r|] ~ RecIO.Ref IntBoolFormula'
  , [f|a|] ~ IntFormula (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula')
  , Recur (K n (RecIO.Rec n')) (RecIntBool'D d)
  ) =>
  Recur (K n (RecIntBool' n')) d
  where
  recur algebra act =
    recur @(K n (RecIO.Rec n')) @(RecIntBool'D d)
      (\p r (IntBoolFormula' fr) -> algebra p r fr)
      act

data RecIntBool'D d
type instance Definition (RecIntBool'D d) = Name "a" IntBoolFormula' :+: Follow d

type RecM2In1 r1 r2 b1 b2 = ReaderT (() -> r1 -> RecM2 r1 r2 b1 b2 b1) CIO
type RecM2In2 r1 r2 b1 b2 = ReaderT (() -> r2 -> RecM2 r1 r2 b1 b2 b2) (RecM2In1 r1 r2 b1 b2)

newtype RecM2 r1 r2 b1 b2 c = RecM2
  {unRecM2 :: RecM2In2 r1 r2 b1 b2 c}
  deriving newtype (Functor, Applicative, Monad)

instance GMonadTrans (RecM2 r1 r2 b1 b2) (RecM2In2 r1 r2 b1 b2) where
  glift = RecM2

data BoolIntE
type instance Definition BoolIntE =
  Name "p" ()
  :+: Name "r" BoolIntFormula
  :+: Name "a" (BoolFormula IntBoolFormula BoolIntFormula)
  :+: Name "m" (Kindy CIO)
  :+: Name "bx" Bool
  :+: Name "bm" (Kindy (RecM2 BoolIntFormula IntBoolFormula Bool Int))
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: Name "c" (Kindy (RecM2In1 BoolIntFormula IntBoolFormula Bool Int))
  :+: Name "recurd" (Kindy RecurD)
  :+: End

data IntBoolE
type instance Definition IntBoolE =
  Name "p" ()
  :+: Name "r" IntBoolFormula
  :+: Name "a" (IntFormula BoolIntFormula IntBoolFormula)
  :+: Name "m" (Kindy (RecM2In1 BoolIntFormula IntBoolFormula Bool Int))
  :+: Name "bx" Int
  :+: Name "bm" (Kindy (RecM2 BoolIntFormula IntBoolFormula Bool Int))
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: Name "c" (Kindy (RecM2In2 BoolIntFormula IntBoolFormula Bool Int))
  :+: Name "recurd" (Kindy RecurD)
  :+: End

data BoolInt'E
type instance Definition BoolInt'E =
  Name "p" ()
  :+: Name "r" (RecIO.Ref BoolIntFormula')
  :+: Name "a" (BoolFormula (RecIO.Ref IntBoolFormula') (RecIO.Ref BoolIntFormula'))
  :+: Name "m" (Kindy CIO)
  :+: Name "bx" Bool
  :+: Name "bm" (Kindy (RecM2 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: Name "c" (Kindy (RecM2In1 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
  :+: Name "recurd" (Kindy RecurD)
  :+: End

data IntBool'E
type instance Definition IntBool'E =
  Name "p" ()
  :+: Name "r" (RecIO.Ref IntBoolFormula')
  :+: Name "a" (IntFormula (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula'))
  :+: Name "m" (Kindy (RecM2In1 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
  :+: Name "bx" Int
  :+: Name "bm" (Kindy (RecM2 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
  :+: Name "b" ([fsk|bm|] [gs|bx|])
  :+: Name "c" (Kindy (RecM2In2 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
  :+: Name "recurd" (Kindy RecurD)
  :+: End

fix2 :: Bool -> Bool -> BoolIntFormula
fix2 val1 val2 = BoolIntFormula $ And
  (BoolIntFormula $ Not $ BoolIntFormula $ And leq (BoolIntFormula $ BoolLit val1))
  (BoolIntFormula $ And leq (BoolIntFormula $ Not $ BoolIntFormula $ BoolLit val1))
  where
    leq = BoolIntFormula $ Leq count2 (IntBoolFormula $ IntLit 2)
    count = IntBoolFormula $ Count [tv2, BoolIntFormula $ BoolLit True, tv2]
    count2 = IntBoolFormula $ Plus count count
    tv2 = BoolIntFormula $ And (BoolIntFormula $ BoolLit True) (BoolIntFormula $ BoolLit val2)

iorefg2 :: Bool -> Bool -> IO (RecIO.Ref BoolIntFormula')
iorefg2 val1 val2 = do
  v2 <- RecIO.buildTopo 0 $ BoolIntFormula' $ BoolLit val2
  print ("v2", v2)
  t <- RecIO.buildTopo 0 $ BoolIntFormula' $ BoolLit True
  print ("t", t)
  tv2 <- RecIO.buildTopo 1 $ BoolIntFormula' $ And t v2
  print ("tv2", tv2)
  count <- RecIO.buildTopo 2 $ IntBoolFormula' $ Count [tv2, t, tv2]
  print ("count", count)
  plus <- RecIO.buildTopo 3 $ IntBoolFormula' $ Plus count count
  print ("plus", plus)
  l1 <- RecIO.buildTopo 0 $ IntBoolFormula' $ IntLit 2
  print ("l1", l1)
  leq <- RecIO.buildTopo 3 $ BoolIntFormula' $ Leq plus l1
  print ("leq", leq)
  v1 <- RecIO.buildTopo 0 $ BoolIntFormula' $ BoolLit val1
  print ("v1", v1)
  nv1 <- RecIO.buildTopo 1 $ BoolIntFormula' $ Not v1
  print ("nv1", nv1)
  leqv1 <- RecIO.buildTopo 4 $ BoolIntFormula' $ And leq v1
  print ("leqv1", leqv1)
  leqnv1 <- RecIO.buildTopo 4 $ BoolIntFormula' $ And leq nv1
  print ("leqnv1", leqnv1)
  nleqv1 <- RecIO.buildTopo 5 $ BoolIntFormula' $ Not leqv1
  print ("nleqv1", nleqv1)
  RecIO.buildTopo 6 $ BoolIntFormula' $ And nleqv1 leqnv1

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

  -- Test recursion of Free

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

  -- Test recursion of IORefGraph

  iorefg1_True <- iorefg1_val True
  1 <- runCIO do
    False <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @GraphE
      (boolAlgebra @(D1 GraphE))
      (unRecM $ cataRec @(RecBool (D1 GraphE) _ _) $ iorefg1_True)
    return ()

  iorefg1_False <- iorefg1_val False
  1 <- runCIO do
    True <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @GraphE
      (boolAlgebra @(D1 GraphE))
      (unRecM $ cataRec @(RecBool (D1 GraphE) _ _) $ iorefg1_False)
    return ()

  iorefg1_var' <- iorefg1_var
  1 <- runCIO do
    False <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @VGraphE
      (boolAlgebraVar @(D1 VGraphE) (\0 -> True))
      (unRecM $ cataRec @(RecBool (D1 VGraphE) _ _) $ iorefg1_var')
    return ()

  1 <- runCIO do
    True <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @VGraphE
      (boolAlgebraVar @(D1 VGraphE) (\0 -> False))
      (unRecM $ cataRec @(RecBool (D1 VGraphE) _ _) $ iorefg1_var')
    return ()

  -- Test mutual recursion of "Fix"

  6 <- runCIO do
    True <- cata @(K (Succ Zero) RecBoolInt) @BoolIntE
      (boolAlgebra @(D2 IntBoolE BoolIntE)) $ do
        cata @(K (Succ (Succ Zero)) RecIntBool) @IntBoolE
          (intAlgebra @(D2 IntBoolE BoolIntE)) $ do
            (unRecM2 $ cataRec @(RecBool (D2 IntBoolE BoolIntE) _ _) (fix2 False False))
    return ()

  6 <- runCIO do
    False <- cata @(K (Succ Zero) RecBoolInt) @BoolIntE
      (boolAlgebra @(D2 IntBoolE BoolIntE)) $ do
        cata @(K (Succ (Succ Zero)) RecIntBool) @IntBoolE
          (intAlgebra @(D2 IntBoolE BoolIntE)) $ do
            (unRecM2 $ cataRec @(RecBool (D2 IntBoolE BoolIntE) _ _) (fix2 True False))
    return ()

  6 <- runCIO do
    False <- cata @(K (Succ Zero) RecBoolInt) @BoolIntE
      (boolAlgebra @(D2 IntBoolE BoolIntE)) $ do
        cata @(K (Succ (Succ Zero)) RecIntBool) @IntBoolE
          (intAlgebra @(D2 IntBoolE BoolIntE)) $ do
            (unRecM2 $ cataRec @(RecBool (D2 IntBoolE BoolIntE) _ _) (fix2 False True))
    return ()

  -- Test mutual recursion of IORefGraph

  iorefg2_00 <- iorefg2 False False
  2 <- runCIO do
    True <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
      (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
        cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
          (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
            (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_00)
    return ()

  iorefg2_10 <- iorefg2 True False
  2 <- runCIO do
    False <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
      (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
        cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
          (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
            (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_10)
    return ()

  iorefg2_01 <- iorefg2 False True
  2 <- runCIO do
    False <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
      (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
        cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
          (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
            (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_01)
    return ()

  -- Test two-way recursion of IORefGraph
  -- TODO

  return ()
