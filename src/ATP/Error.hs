{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}

{-|
Module       : ATP.Error
Description  : Monads and monad transformers for computations with errors.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Error (
  Error(..),
  Partial,
  PartialT(..),
  liftPartial,
  timeoutError,
  parsingError,
  proofError,
  otherError
) where

import Control.Monad.Except (MonadTrans, ExceptT(..), MonadError(..), runExcept)
import Data.Functor.Identity (Identity)
import Data.Text (Text)
import qualified Data.Text as T (pack)


-- | The error that might occur while reconstructing the proof.
data Error
  = Timeout
  -- ^ The theorem prover terminated by the timeout without producing a proof.
  | ParsingError Text
  -- ^ The output of the theorem prover is not a well-formed TSTP.
  | ProofError Text
  -- ^ The proof returned by the theorem prover is not well-formed.
  | OtherError Text
  -- ^ An uncategorized error.
  deriving (Show, Eq, Ord)

-- | A monad transformer that adds failing with an @'Error'@ to other monads.
newtype PartialT m a = PartialT {
  runPartialT :: ExceptT Error m a
} deriving (Show, Eq, Ord, Functor, Applicative, Monad, MonadTrans, MonadError Error)

instance Monad m => MonadFail (PartialT m) where
  fail = otherError

-- | The type of computations that might fail with an @'Error'@.
type Partial = PartialT Identity

-- | Extractor for computations in the @'Partial'@ monad.
liftPartial :: Partial a -> Either Error a
liftPartial = runExcept . runPartialT

-- | A smart constructor for a computation failed with a @'Timeout'@.
timeoutError :: Monad m => PartialT m a
timeoutError = PartialT (throwError Timeout)

-- | A smart constructor for a computation failed with a @'ParsingError'@.
parsingError :: Monad m => String -> PartialT m a
parsingError = PartialT . throwError . ParsingError . T.pack

-- | A smart constructor for a computation failed with a @'ProofError'@.
proofError :: Monad m => String -> PartialT m a
proofError = PartialT . throwError . ProofError . T.pack

-- | A smart constructor for a computation failed with a @'OtherError'@.
otherError :: Monad m => String -> PartialT m a
otherError = PartialT . throwError . OtherError . T.pack
