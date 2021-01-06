{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}

{-|
Module       : ATP.Error
Description  : Monads and monad transformers for computations with errors.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Monads and monad transformers for computations with errors.
-}

module ATP.Error (
  Error(..),
  Partial,
  PartialT(..),
  liftPartial,
  isSuccess,
  isFailure,
  exitCodeError,
  timeLimitError,
  memoryLimitError,
  parsingError,
  proofError,
  otherError
) where

import Control.Monad.Except (MonadTrans, ExceptT(..), MonadError(..), runExcept)
import Data.Either (isLeft, isRight)
import Data.Functor.Identity (Identity)
import Data.Text (Text)
import qualified Data.Text as T (pack)


-- | The error that might occur while reconstructing the proof.
data Error
  = ExitCodeError Int Text
  -- ^ The theorem prover terminated with a non-zero exit code.
  | TimeLimitError
  -- ^ The theorem prover reached the time limit without producing a solution.
  | MemoryLimitError
  -- ^ The theorem prover reached the memory limit without producing a solution.
  | ParsingError Text
  -- ^ The output of the theorem prover is not a well-formed TSTP.
  | ProofError Text
  -- ^ The proof returned by the theorem prover is not well-formed.
  | OtherError Text
  -- ^ An uncategorized error.
  deriving (Show, Eq, Ord)

-- | The type of computations that might fail with an @'Error'@.
type Partial = PartialT Identity

-- | A monad transformer that adds failing with an @'Error'@ to other monads.
newtype PartialT m a = PartialT {
  runPartialT :: ExceptT Error m a
} deriving (Show, Eq, Ord, Functor, Applicative, Monad, MonadTrans, MonadError Error)

-- | Extractor for computations in the @'Partial'@ monad.
liftPartial :: Partial a -> Either Error a
liftPartial = runExcept . runPartialT

-- | Check whether a partial computation resulted successfully.
isSuccess :: Partial a -> Bool
isSuccess = isRight . liftPartial

-- | Check whether a partial computation resulted with an error.
isFailure :: Partial a -> Bool
isFailure = isLeft . liftPartial

-- | A smart constructor for a computation failed with an @'ExitCodeError'@.
exitCodeError :: Monad m => Int -> Text -> PartialT m a
exitCodeError exitCode err = PartialT (throwError $ ExitCodeError exitCode err)

-- | A smart constructor for a computation failed with a @'TimeLimitError'@.
timeLimitError :: Monad m => PartialT m a
timeLimitError = PartialT (throwError TimeLimitError)

-- | A smart constructor for a computation failed with a @'MemoryLimitError'@.
memoryLimitError :: Monad m => PartialT m a
memoryLimitError = PartialT (throwError MemoryLimitError)

-- | A smart constructor for a computation failed with a @'ParsingError'@.
parsingError :: Monad m => String -> PartialT m a
parsingError = PartialT . throwError . ParsingError . T.pack

-- | A smart constructor for a computation failed with a @'ProofError'@.
proofError :: Monad m => String -> PartialT m a
proofError = PartialT . throwError . ProofError . T.pack

-- | A smart constructor for a computation failed with a @'OtherError'@.
otherError :: Monad m => String -> PartialT m a
otherError = PartialT . throwError . OtherError . T.pack
