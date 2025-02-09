{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module FreeImpl where

import Control.Exception
import Control.Monad
import Control.Monad.Free
import Control.Monad.Free.Church
import Data.IORef
import GHC.Generics
import System.Random

data LogLevel = Info | Error
type Message = String

-- Algebra (interface) for the LoggerL Free monadic language with only 1 method
data LoggerF next where
  LogMessage ∷ LogLevel → Message → (() → next) → LoggerF next

-- Functor instance needed for the Free machinery
instance Functor LoggerF where
  fmap f (LogMessage lvl msg next) = LogMessage lvl msg (f . next)

-- Free monadic language
#ifdef CHURCH
type Logger a = F LoggerF a
#else
type Logger a = Free LoggerF a
#endif

data AppF next where
  GetRandomInt ∷ (Int, Int) → (Int → next) → AppF next
  EvalLogger ∷ Logger () → (() → next) → AppF next
  RunIO ∷ IO a → (a → next) → AppF next
  ThrowException ∷ ∀ a e next. Exception e ⇒ e → (a → next) → AppF next
  RunSafely ∷ App a → (Either String a → next) → AppF next

instance Functor AppF where
  fmap f (GetRandomInt range next) = GetRandomInt range (f . next)
  fmap f (EvalLogger logAct next) = EvalLogger logAct (f . next)
  fmap f (RunIO act next) = RunIO act (f . next)
  fmap f (ThrowException exc next) = ThrowException exc (f . next)
  fmap f (RunSafely act next) = RunSafely act (f . next)

#ifdef CHURCH
type App a = F AppF a
#else
type App a = Free AppF a
#endif

-- Interpreting function
interpretAppF ∷ AppF a → IO a
interpretAppF (EvalLogger loggerAct next) = next <$> runLogger loggerAct
interpretAppF (GetRandomInt range next) = next <$> randomRIO range
interpretAppF (RunIO ioAct next) = next <$> ioAct
interpretAppF (ThrowException exc next) = throwIO exc
interpretAppF (RunSafely act next) = do
  eResult ← try $ runApp act
  pure $ next $ case eResult of
    Left (err ∷ SomeException) → Left $ show err
    Right r → Right r

-- Interpreter entry point
runApp ∷ App a → IO a
#ifdef CHURCH
runApp = foldF interpretAppF
#else
runApp = foldFree interpretAppF
#endif

-- Simple console logger
interpretLoggerF ∷ LoggerF a → IO a
interpretLoggerF (LogMessage lvl msg next) = next <$> putStrLn msg

runLogger ∷ Logger a → IO a
#ifdef CHURCH
runLogger = foldF interpretLoggerF
#else
runLogger = foldFree interpretLoggerF
#endif

runIO ∷ IO a → App a
runIO ioAct = liftF $ RunIO ioAct id

-- Log message with Info level.
logInfo ∷ Message → App ()
logInfo msg = evalLogger (logMessage Info msg)

-- Log message with Error level.
logError ∷ Message → App ()
logError msg = evalLogger (logMessage Error msg)

-- Helper function to wrap LoggerF method
logMessage ∷ LogLevel → Message → Logger ()
logMessage lvl msg = liftF $ LogMessage lvl msg id

-- Helper function to wrap AppF method
evalLogger ∷ Logger () → App ()
evalLogger logger = liftF $ EvalLogger logger id

getRandomInt ∷ (Int, Int) → App Int
getRandomInt range = liftF $ GetRandomInt range id

throwException ∷ ∀ a e. Exception e ⇒ e → App a
throwException ex = liftF $ ThrowException ex id

runSafely ∷ App a → App (Either String a)
runSafely act = liftF $ RunSafely act id

printRandomFactorial ∷ App ()
printRandomFactorial = do
  n ← getRandomInt (1, 10)
  logInfo $ show $ fact n

printRandomFibonacci ∷ App ()
printRandomFibonacci = do
  n ← getRandomInt (1, 10)
  logInfo $ show $ fib !! n

printRandomFactorialFibonacci ∷ App ()
printRandomFactorialFibonacci = do
  printRandomFactorial
  printRandomFibonacci

fact ∷ Int → Int
fact 0 = 1
fact n = n * fact (n - 1)

fib ∷ [Int]
fib = 0 : 1 : zipWith (+) fib (tail fib)

data AppException = InvalidOperation String
  deriving (Eq, Ord, Show, Generic, Exception)

unsafeScenario ∷ App Int
unsafeScenario = do
  val ← getRandomInt (1, 90)
  case () of
    _
      | val <= 30 → pure 0
      | val <= 60 → pure val
      | otherwise → throwException $ InvalidOperation "Failed with 1/3 chance"

safeScenario ∷ App ()
safeScenario = do
  eVal ← runSafely unsafeScenario
  case eVal of
    Left err → logError $ "Exception got: " <> err
    Right val → logInfo $ "Value got: " <> show val

newtype RandomValueMocks = RandomValueMocks {curVal ∷ IORef [Int]}

interpretAppF' ∷ RandomValueMocks → AppF a → IO a
interpretAppF' mocks (EvalLogger loggerAct next) = next <$> runLogger loggerAct
interpretAppF' mocks (RunIO ioAct next) = next <$> ioAct
interpretAppF' mocks (ThrowException exc next) = throwIO exc
interpretAppF' mocks (RunSafely act next) = do
  eResult ← try $ runApp' mocks act
  pure $ next $ case eResult of
    Left (err ∷ SomeException) → Left $ show err
    Right r → Right r
interpretAppF' mocks (GetRandomInt range next) = do
  x : xs ← readIORef (curVal mocks) -- getting the next mock
  writeIORef (curVal mocks) xs
  pure $ next $ x

runApp' ∷ RandomValueMocks → App a → IO a
#ifdef CHURCH
runApp' mocks = foldF (interpretAppF' mocks)
#else
runApp' mocks = foldFree (interpretAppF' mocks)
#endif

flow ∷ IORef Int → App ()
flow ref = do
  val' ← runIO $ readIORef ref
  val ← getRandomInt (1, 100)
  runIO $ writeIORef ref $ val' + val

benchmark ∷ Int → IO ()
benchmark ops = do
  ref ← newIORef 0
  void $ runApp (replicateM_ ops $ flow ref)
  val ← readIORef ref
  print val
