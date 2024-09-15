{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module DictImpl where

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Data.IORef
import Data.Kind
import GHC.Generics hiding ((:+:))
import InversionOfControl.ExplicitMonadFn
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import System.Random

data LogLevel = Info | Error
type Message = String

type GetRandomInt d m = E d "getRandomInt" (Int, Int) Int m
type RunIO d m a = E d "runIO" (IO a) a m
type LogMessage d m = E d "logMessage" (LogLevel, Message) () m
type ThrowException d m e a = E d "throwException" e a m
type RunSafely d m a = E d "runSafely" (m a) (Either String a) m

type Logger d m = DMonadFn (LogMessage d m)
type App d m =
  ( DMonadFn (GetRandomInt d m)
  , ∀ a. DMonadFn (RunIO d m a)
  , ∀ a e. Exception e ⇒ DMonadFn (ThrowException d m e a) ∷ Constraint
  , ∀ a. DMonadFn (RunSafely d m a)
  , Logger d m
  )

data LogMessage1
instance MonadFn0 LogMessage1 (LogLevel, Message) () IO where
  monadfn0 (lvl, msg) = putStrLn msg

data GetRandomInt1
instance MonadFn0 GetRandomInt1 (Int, Int) Int IO where
  monadfn0 range = randomRIO range

data RunIO1
instance MonadFn0 RunIO1 (IO a) a IO where
  monadfn0 act = act

data ThrowException1
instance Exception e ⇒ MonadFn0 ThrowException1 e a IO where
  monadfn0 = throwIO

data RunSafely1
instance MonadFn0 RunSafely1 (IO a) (Either String a) IO where
  monadfn0 act = do
    eResult ← try act
    pure case eResult of
      Left (err ∷ SomeException) → Left $ show err
      Right r → Right r

data LogD
type instance Definition LogD = Name "logMessage" LogMessage1 :+: End

data AppD
type instance
  Definition AppD =
    Name "getRandomInt" GetRandomInt1
      :+: Name "runIO" RunIO1
      :+: Name "throwException" ThrowException1
      :+: Name "runSafely" RunSafely1
      :+: Follow LogD

printRandomFactorial ∷ ∀ d m. App d m ⇒ m ()
printRandomFactorial = do
  n ← dmonadfn @(GetRandomInt d _) (1, 10)
  dmonadfn @(LogMessage d _) (Info, show $ fact n)

printRandomFibonacci ∷ ∀ d m. App d m ⇒ m ()
printRandomFibonacci = do
  n ← dmonadfn @(GetRandomInt d _) (1, 10)
  dmonadfn @(LogMessage d _) (Info, show $ fib !! n)

printRandomFactorialFibonacci ∷ ∀ d m. App d m ⇒ m ()
printRandomFactorialFibonacci = do
  printRandomFactorial @d
  printRandomFibonacci @d

fact ∷ Int → Int
fact 0 = 1
fact n = n * fact (n - 1)

fib ∷ [Int]
fib = 0 : 1 : zipWith (+) fib (tail fib)

data AppException = InvalidOperation String
  deriving (Eq, Ord, Show, Generic, Exception)

unsafeScenario ∷ ∀ d m. App d m ⇒ m Int
unsafeScenario = do
  val ← dmonadfn @(GetRandomInt d _) (1, 90)
  case () of
    _
      | val <= 30 → pure 0
      | val <= 60 → pure val
      | otherwise → dmonadfn @(ThrowException d _ _ _) $ InvalidOperation "Failed with 1/3 chance"

safeScenario ∷ ∀ d m. App d m ⇒ m ()
safeScenario = do
  eVal ← dmonadfn @(RunSafely d _ _) (unsafeScenario @d)
  case eVal of
    Left err → dmonadfn @(LogMessage d _) (Error, "Exception got: " ++ err)
    Right val → dmonadfn @(LogMessage d _) (Info, "Value got: " ++ show val)

newtype RandomValueMocks = RandomValueMocks (IORef [Int])
type MockApp = ReaderT RandomValueMocks IO

data GetRandomIntMocked
instance MonadFn0 GetRandomIntMocked (Int, Int) Int MockApp where
  monadfn0 _ = do
    RandomValueMocks ref ← ask
    lift do
      x : xs ← readIORef ref
      writeIORef ref xs
      pure x

instance MonadFn0 RunSafely1 (MockApp a) (Either String a) MockApp where
  monadfn0 act = do
    env ← ask
    eResult ← lift do try $ runReaderT act env
    pure case eResult of
      Left (err ∷ SomeException) → Left $ show err
      Right r → Right r

data MockAppD
type instance
  Definition MockAppD =
    Name "getRandomInt" GetRandomIntMocked
      :+: Name "runSafely" RunSafely1
      :+: Follow (LiftUp AppD)

runMockApp ∷ RandomValueMocks → MockApp a → IO a
runMockApp mocks act = runReaderT act mocks

flow ∷ ∀ d m. App d m ⇒ IORef Int → m ()
flow ref = do
  val' ← dmonadfn @(RunIO d _ _) $ readIORef ref
  val ← dmonadfn @(GetRandomInt d _) (1, 100)
  dmonadfn @(RunIO d _ _) $ writeIORef ref $ val' + val

benchmark ∷ Int → IO ()
benchmark n = do
  ref ← newIORef 0
  replicateM_ n do flow @AppD ref
  val ← readIORef ref
  print val
