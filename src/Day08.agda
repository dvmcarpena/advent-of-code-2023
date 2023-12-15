{-# OPTIONS --cubical-compatible --safe #-}

module Day08 where

-- Imports

open import Function.Base using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _*_)
open import Data.Nat.Show renaming (show to ℕ-show)
open import Data.String as String using (String)

open import Utils using (Runner; mkRunner; module Utils)

-- Data

Parsed : Set
Parsed = {!   !}

example-input : String
example-input = {!   !}

example-parsed : Parsed
example-parsed = {!   !}

example-output1 : ℕ
example-output1 = {!   !}

example-output2 : ℕ
example-output2 = 0

-- Parse

parse-input : String → Maybe Parsed
parse-input = {!   !}

_ : parse-input example-input ≡ just example-parsed
_ = refl

-- Solvers

solve1 : String → Maybe ℕ
solve1 = Maybe.map (solve)  ∘ parse-input
  where
    solve : Parsed → ℕ
    solve = {!   !}

solve2 : String → Maybe ℕ
solve2 = Maybe.map (solve)  ∘ parse-input
  where
    solve : Parsed → ℕ
    solve = λ _ → 0

_ : solve1 example-input ≡ just example-output1
_ = refl

_ : solve2 example-input ≡ just example-output2
_ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day08" "Day 08"
  