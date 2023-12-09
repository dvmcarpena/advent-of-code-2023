{-# OPTIONS --with-K --safe #-}

module Day03 where

-- Imports

open import Function.Base using (_∘_; _$_)
open import Relation.Nullary.Decidable using (True)
open import Data.Product using (_×_; _,_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)
open import Data.String as String using (String)
import Data.Char.Properties as Charₚ
open import Text.Regex Charₚ.≤-decPoset using (Exp; _∈?_; _∈_)

open import utils as Utils using (Runner; mkRunner; module Utils)
-- open Utils.Expression using (Exp-ℕ; Exp-from-String')
open Utils.Parser using (parse-ℕ; generic-parser-by-lines)

-- open import Function.Base using (_$_; _∘_; id)
-- open import Data.Product using (_×_; _,_; <_,_>)
-- open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
-- open import Relation.Nullary using (Dec; yes; no)
-- open import Relation.Nullary.Decidable using (True; False; from-yes)
-- open import Relation.Binary using (DecPoset)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Data.Bool.Base using (Bool; if_then_else_; true; false; _∧_; _∨_; not)
-- open import Data.Maybe as Maybe using (Maybe; nothing; just)
-- open import Data.Char.Base as Char using (Char)
-- import Data.Char.Properties as Charₚ
-- open import Data.List as List using (List; _∷_; [])
-- open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
-- open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _≤ᵇ_)
-- open import Data.Nat.Properties as ℕₚ
-- open import Data.List.Extrema ℕₚ.≤-totalOrder renaming (max to Listℕ-max)
-- open import Data.String as String using (String; _++_)
-- open import Relation.Binary.Properties.DecTotalOrder ℕₚ.≤-decTotalOrder renaming (≥-decTotalOrder to ℕ-≥-decTotalOrder)
-- open import Data.List.Sort.MergeSort ℕ-≥-decTotalOrder renaming (sort to Listℕ-sort-decreasing)
-- open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)
-- open import Data.List.Relation.Unary.All
-- open import Data.Product as Product using (∃-syntax; _,′_; proj₁; proj₂)
-- import Text.Regex.Base (DecPoset.preorder Charₚ.≤-decPoset) as R
-- open import Text.Regex Charₚ.≤-decPoset

-- open import utils as Utils using (Runner; mkRunner)
-- open Utils.Expression using (Exp-ℕ; Exp-from-String')
-- open Utils.Parser using (parse-ℕ; generic-parser-by-lines)
-- open import utils-with-k using (parse-6-cases; Exp-star-elimination)

-- Data

Parsed : Set
Parsed = (List (ℕ × ℕ)) × (List (ℕ × ℕ × ℕ))

example-input : String
example-input = "467..114..\n...*......\n..35..633.\n......#...\n617*......\n.....+.58.\n..592.....\n......755.\n...$.*....\n.664.598.."

example-parsed : Parsed
example-parsed = ((2 , 4) ∷ (4 , 7) ∷ (5 , 4) ∷ (6 , 6) ∷ (9 , 4) ∷ (9 , 6) ∷ []) 
               , ((467 , 1  , 1) ∷ 
                  (114 , 1  , 6) ∷ 
                  (35  , 3  , 3) ∷ 
                  (633 , 3  , 7) ∷ 
                  (617 , 5  , 1) ∷ 
                  (58  , 6  , 8) ∷ 
                  (592 , 7  , 3) ∷ 
                  (755 , 8  , 7) ∷ 
                  (664 , 10 , 2) ∷ 
                  (598 , 10 , 6) ∷ [])

example-output1 : ℕ
example-output1 = 4361

-- example-output2 : ℕ
-- example-output2 = ?

-- Parse

valid-line : Exp
valid-line = {!   !}

-- _ : True ((String.toList "467..*..114..") ∈? valid-line)
-- _ = _

parse-line : ∀ {s} → (s ∈ valid-line) → (List ℕ) × (List (ℕ × ℕ))
parse-line x = {!   !}

parse-input : String → Maybe Parsed
parse-input = Maybe.map (join-rows ∘ List⁺.toList) ∘ generic-parser-by-lines valid-line parse-line
    where
        add-row : (ℕ × (List ℕ) × (List (ℕ × ℕ))) → (List (ℕ × ℕ)) × (List (ℕ × ℕ × ℕ))
        add-row (r , ss , ns) = List.map (λ c → (r , c)) ss , List.map (λ (n , c) → (n , r , c)) ns

        concat : List Parsed → Parsed
        concat [] = [] , []
        concat ((s1 , n1) ∷ ps) = (λ (sn , nn) → (s1 List.++ sn) , (n1 List.++ nn)) $ concat ps

        join-rows : List ((List ℕ) × (List (ℕ × ℕ))) → Parsed
        join-rows = concat ∘ List.map add-row ∘ Utils.enumerate

-- _ : parse-input example-input ≡ just example-parsed
-- _ = refl

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
    solve x = 0

-- _ : solve1 example-input ≡ just example-output1
-- _ = refl

-- _ : solve2 example-input ≡ just example-output2
-- _ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day02" "Day 02"
