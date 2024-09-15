{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module MonadImpl where

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Data.IORef
import GHC.Generics
import System.Random

data LogLevel = Info | Error
type Message = String

class Monad m ⇒ Logger m where
  logMessage ∷ LogLevel → Message → m ()

class Logger m ⇒ App m where
  getRandomInt ∷ (Int, Int) → m Int
  runIO ∷ IO a → m a
  throwException ∷ Exception e ⇒ e → m a
  runSafely ∷ m a → m (Either String a)

instance Logger IO where
  logMessage lvl msg = putStrLn msg

instance App IO where
  getRandomInt range = randomRIO range
  runIO ioAct = ioAct
  throwException ex = throwIO ex
  runSafely act = do
    eResult ← try act
    pure $ case eResult of
      Left (err ∷ SomeException) → Left $ show err
      Right r → Right r

logInfo ∷ Logger m ⇒ Message → m ()
logInfo msg = logMessage Info msg

logError ∷ Logger m ⇒ Message → m ()
logError msg = logMessage Error msg

printRandomFactorial ∷ App m ⇒ m ()
printRandomFactorial = do
  n ← getRandomInt (1, 10)
  logInfo $ show $ fact n

printRandomFibonacci ∷ App m ⇒ m ()
printRandomFibonacci = do
  n ← getRandomInt (1, 10)
  logInfo $ show $ fib !! n

fact ∷ Int → Int
fact 0 = 1
fact n = n * fact (n - 1)

fib ∷ [Int]
fib = 0 : 1 : zipWith (+) fib (tail fib)

printRandomFactorialFibonacci ∷ App m ⇒ m ()
printRandomFactorialFibonacci = do
  printRandomFactorial
  printRandomFibonacci

data AppException = InvalidOperation String
  deriving (Eq, Ord, Show, Generic, Exception)

unsafeScenario ∷ App m ⇒ m Int
unsafeScenario = do
  val ← getRandomInt (1, 90)
  case () of
    _
      | val <= 30 → pure 0
      | val <= 60 → pure val
      | otherwise → throwException $ InvalidOperation "Failed with 1/3 chance"

safeScenario ∷ App m ⇒ m ()
safeScenario = do
  eVal ← runSafely unsafeScenario
  case eVal of
    Left err → logError $ "Exception got: " <> err
    Right val → logInfo $ "Value got: " <> show val

newtype RandomValueMocks = RandomValueMocks (IORef [Int])

newtype MockApp a = MockApp (ReaderT RandomValueMocks IO a)
  deriving newtype (Functor, Applicative, Monad)

instance Logger MockApp where -- Free has reused this definition.
  logMessage lvl msg = MockApp do lift do putStrLn msg

instance App MockApp where
  getRandomInt range = MockApp do
    RandomValueMocks ref ← ask
    lift do
      x : xs ← readIORef ref
      writeIORef ref xs
      pure x
  runIO ioAct = MockApp do lift ioAct
  throwException ex = MockApp do lift do throwIO ex
  runSafely (MockApp act) = MockApp do
    env ← ask
    eResult ← lift do try $ runReaderT act env
    pure $ case eResult of
      Left (err ∷ SomeException) → Left $ show err
      Right r → Right r

runMockApp ∷ RandomValueMocks → MockApp a → IO a
runMockApp mocks (MockApp act) = runReaderT act mocks

flow ∷ App m ⇒ IORef Int → m ()
flow ref = do
  val' ← runIO $ readIORef ref
  val ← getRandomInt (1, 100)
  runIO $ writeIORef ref $ val' + val

benchmark ∷ Int → IO ()
benchmark ops = do
  ref ← newIORef 0
  replicateM_ ops $ flow ref
  val ← readIORef ref
  print val
