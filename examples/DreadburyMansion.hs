{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : DreadburyMansion
Description  : A logical puzzle.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Someone who lives in Dreadbury Mansion killed Aunt Agatha. Agatha, the butler,
and Charles live in Dreadbury Mansion, and are the only people who live therein.
A killer always hates his victim, and is never richer than his victim. Charles
hates no one that Aunt Agatha hates. Agatha hates everyone except the butler.
The butler hates everyone not richer than Aunt Agatha. The butler hates everyone
Aunt Agatha hates. No one hates everyone. Agatha is not the butler.
Therefore: Agatha killed herself.

Source: http://tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=PUZ&File=PUZ001+1.p
-}

module DreadburyMansion where

import ATP

agatha, butler, charles :: Constant
agatha  = "agatha"
butler  = "butler"
charles = "charles"

lives :: UnaryPredicate
lives = UnaryPredicate "lives"

killed, hates, richer :: BinaryPredicate
killed = BinaryPredicate "killed"
hates  = BinaryPredicate "hates"
richer = BinaryPredicate "richer"

dreadburyMansion :: Theorem
dreadburyMansion = puzzle |- clue
  where
    puzzle = [
        -- Someone who lives in Dreadbury Mansion killed Aunt Agatha.
        exists $ \x -> lives x /\ x `killed` agatha,

        -- Agatha, the butler, and Charles live in Dreadbury Mansion,
        lives agatha /\ lives butler /\ lives charles,

        -- and are the only people who live therein.
        forall $ \x -> lives x ==> x === agatha \/ x === butler \/ x === charles,

        -- A killer always hates his victim,
        forall $ \x y -> x `killed` y ==> x `hates` y,

        -- and is never richer than his victim.
        forall $ \x y -> x `killed` y ==> neg (x `richer` y),

        -- Charles hates no one that Aunt Agatha hates.
        forall $ \x -> agatha `hates` x ==> neg (charles `hates` x),

        -- Agatha hates everyone except the butler.
        forall $ \x -> x =/= butler ==> agatha `hates` x,

        -- The butler hates everyone not richer than Aunt Agatha.
        forall $ \x -> neg (x `richer` agatha) ==> butler `hates` x,

        -- The butler hates everyone Aunt Agatha hates.
        forall $ \x -> agatha `hates` x ==> butler `hates` x,

        -- No one hates everyone.
        forall $ \x -> exists $ \y -> neg (x `hates` y),

        -- Agatha is not the butler.
        agatha =/= butler
      ]

    -- Agatha killed herself.
    clue = killed agatha agatha
