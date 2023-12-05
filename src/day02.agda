{-# OPTIONS --with-K --safe #-}

module day02 where

-- Imports

open import Function.Base using (_$_; _∘_; id)
open import Data.Product using (_×_; _,_; <_,_>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool.Base using (Bool)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Char.Base as Char using (Char)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _≤ᵇ_)
open import Data.Nat.Properties as ℕₚ
open import Data.String as String using (String; _++_)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
open import Data.List.Extrema ℕₚ.≤-totalOrder renaming (max to Listℕ-max)
open import Relation.Binary.Properties.DecTotalOrder ℕₚ.≤-decTotalOrder renaming (≥-decTotalOrder to ℕ-≥-decTotalOrder)
open import Data.List.Sort.MergeSort ℕ-≥-decTotalOrder renaming (sort to Listℕ-sort-decreasing)
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Bool.Base using (if_then_else_; true; false; _∧_; _∨_; not)
open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)
open import Data.List.Relation.Unary.All
open import Data.Product as Product using (∃-syntax; _,′_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel; Decidable)
open import Relation.Nullary.Decidable using (True; False; from-yes)
import Data.Char.Properties as Charₚ
open import Relation.Binary using (DecPoset)
open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Text.Regex.Base (DecPoset.preorder Charₚ.≤-decPoset) as Regex using ()
open import Text.Regex Charₚ.≤-decPoset renaming (sum to ∈-sum)

open import utils using (EnrichedRunner; List⁺-propagate-maybe; Maybe-idempotent; duplicate; Exp-reverse; Exp-from-Strings')

-- Data

Output : Set
Output = ℕ

Output-show : Output → String
Output-show = ℕ-show

example-input1 : String
example-input1 = "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green\nGame 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue\nGame 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red\nGame 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red\nGame 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"

example-parsed1 : List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ)))
example-parsed1 = (1 , ((4 , (0 , 3)) ∷⁺ (1 , (2 , 6)) ∷⁺ List⁺.[ (0 , (2 , 0)) ])) 
  ∷⁺ (2 , ((0 , (2 , 1)) ∷⁺ (1 , (3 , 4)) ∷⁺ List⁺.[ (0 , (1 , 1)) ])) 
  ∷⁺ (3 , ((20 , (8 , 6)) ∷⁺ (4 , (13 , 5)) ∷⁺ List⁺.[ (1 , (5 , 0)) ])) 
  ∷⁺ (4 , ((3 , (1 , 6)) ∷⁺ (6 , (3 , 0)) ∷⁺ List⁺.[ (14 , (3 , 15)) ])) 
  ∷⁺ List⁺.[ (5 , (6 , (3 , 1)) ∷⁺ List⁺.[ (1 , (2 , 2)) ]) ]

example-output1 : ℕ
example-output1 = 8

-- example-input2 : String
-- example-input2 = "two1nine\neightwothree\nabcone2threexyz\nxtwone3four\n4nineeightseven2\nzoneight234\n7pqrstsixteen"

-- example-parsed2 : List⁺ (ℕ × ℕ)
-- example-parsed2 = (2 ,′ 9) ∷⁺ (8 ,′ 3) ∷⁺ (1 ,′ 3) ∷⁺ (2 ,′ 4) ∷⁺ (4 ,′ 2) ∷⁺ (1 ,′ 4) ∷⁺ List⁺.[ (7 ,′ 6) ]

-- example-output2 : ℕ
-- example-output2 = 281

-- Parse

parse-input : String → Maybe (List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ))))
parse-input = {!   !}

-- Solvers

solve : List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ))) → ℕ
solve = List.sum ∘ List.map proj₁ ∘ List.boolFilter f ∘ List⁺.toList
  where
    gg : ℕ × ℕ × ℕ → Bool
    gg (r , (g , b)) = (r ≤ᵇ 12) ∧ (g ≤ᵇ 13) ∧ (b ≤ᵇ 14)
    
    f : ℕ × (List⁺ (ℕ × ℕ × ℕ)) → Bool
    f (_ , xs) = List.all gg (List⁺.toList xs)

solve1 : String → Maybe Output
solve1 = Maybe.map (solve)  ∘ parse-input

solve2 : String → Maybe Output
solve2 s = just 0

-- _ : solve (List⁺.[ (1 ,′ 3) ]) ≡ 13
-- _ = refl

-- _ : solve ((5 ,′ 4) ∷⁺ List⁺.[ (1 ,′ 3) ]) ≡ 67
-- _ = refl

_ : solve example-parsed1 ≡ example-output1
_ = refl

-- _ : solve example-parsed2 ≡ example-output2
-- _ = refl

-- Runner

runner : String → String
runner = format-results ∘ < solve1 , solve2 >
  where
    format-result : (Maybe Output) → String
    format-result nothing = "Invalid input format!"
    format-result (just out) = Output-show out
    
    format-results : (Maybe Output) × (Maybe Output) → String
    format-results (out₁ , out₂) = "Part One: " ++ format-result out₁ ++ "\nPart Two: " ++ format-result out₂

enriched-runner : EnrichedRunner
enriched-runner = runner , "day02" , "Day 02" , true
