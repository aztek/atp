{-|
Module       : ATP.FOL
Description  : Syntax of first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Data structures that represent formulas and theorems in first-order logic,
and smart constructors for them.
-}

module ATP.FOL (
  module ATP.FirstOrder.Core,
  module ATP.FirstOrder.Alpha,
  module ATP.FirstOrder.Smart,
  module ATP.FirstOrder.Simplification,
  module ATP.FirstOrder.Occurrence,
  module ATP.FirstOrder.Conversion,
  module ATP.FirstOrder.Derivation
) where

import ATP.FirstOrder.Core
import ATP.FirstOrder.Alpha
import ATP.FirstOrder.Smart
import ATP.FirstOrder.Simplification
import ATP.FirstOrder.Occurrence
import ATP.FirstOrder.Conversion
import ATP.FirstOrder.Derivation
