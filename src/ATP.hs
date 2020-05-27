{-|
Module       : ATP
Description  : Interface to automated theorem provers.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP (
  module ATP.FOL,
  module ATP.Pretty.FOL,
  module ATP.Prove,
  module ATP.Prover
) where

import ATP.FOL
import ATP.Pretty.FOL
import ATP.Prove
import ATP.Prover
