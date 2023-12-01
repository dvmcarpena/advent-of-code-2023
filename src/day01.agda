{-# OPTIONS --without-K --guardedness #-}

module day01 where

-- Imports

open import Function.Base using (_$_; _∘_; id)
open import Data.Product using (_×_; _,_; <_,_>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕₚ
open import Data.String as String using (String; _++_)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Extrema ℕₚ.≤-totalOrder renaming (max to Listℕ-max)
open import Relation.Binary.Properties.DecTotalOrder ℕₚ.≤-decTotalOrder renaming (≥-decTotalOrder to ℕ-≥-decTotalOrder)
open import Data.List.Sort.MergeSort ℕ-≥-decTotalOrder renaming (sort to Listℕ-sort-decreasing)
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Bool.Base using (if_then_else_; true; false)
open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)

open import utils using (EnrichedRunner)

-- Variables

private
  variable
    n : ℕ

-- Data

Input : Set
Input = ℕ

Output : Set
Output = ℕ

Output-show : Output → String
Output-show = ℕ-show

-- Parser

parse-input : (s : String) → Maybe (Input)
parse-input = {!   !}

-- Solvers

solve1 : Input → Output
solve1 = {!   !}

solve2 : Input → Output
solve2 = {!   !}

-- Runner

runner : String → String
runner = try-format-results ∘ solve-output
  where
    solve-output : String → Maybe (Output × Output)
    solve-output = Maybe.map < solve1 , solve2 > ∘ parse-input

    format-results : Output → Output → String
    format-results s₁ s₂ = "Part One: " ++ Output-show s₁ ++ "\nPart Two: " ++ Output-show s₂
    
    try-format-results : Maybe (Output × Output) → String
    try-format-results nothing = "Invalid input format!"
    try-format-results (just (s₁ , s₂)) = format-results s₁ s₂

enriched-runner : EnrichedRunner
enriched-runner = runner , "day01" , "Day 01" , true

-- Testing

example-input : String
example-input = "TODO"

example : Input
example = {!   !}

-- example-parse-input : (parse-input example-input) ≡ (just example)
-- example-parse-input = refl

-- example-solve1 : (solve1 example) ≡ TODO
-- example-solve1 = refl

-- example-solve2 : (solve2 example) ≡ TODO
-- example-solve2 = refl

-- example-runner : (runner example-input) ≡ "Part One: ?\nPart Two: ?"
-- example-runner = refl

-- example-runner-bad-input : (runner "invalid") ≡ "Invalid input format!"
-- example-runner-bad-input = refl
