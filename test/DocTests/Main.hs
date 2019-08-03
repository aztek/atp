{-|
Module       : DocTests.Main
Description  : Runner of doctests.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module Main where

import Test.DocTest (doctest)

main :: IO ()
main = doctest ["-isrc", "-itest", "--fast", "src/ATP/FOL.hs", "src/ATP/Codec/TPTP.hs"]
