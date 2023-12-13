{-# OPTIONS --with-K --safe #-}

module Day04 where

-- Imports

open import Function.Base using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Char as Char using (Char)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _*_; _^_)
open import Data.Nat.Show renaming (show to ℕ-show)
open import Data.String as String using (String)
import Data.Char.Properties as Charₚ
open import Text.Regex Charₚ.≤-decPoset using (Exp; _∈_; singleton; _⋆; _∙_; _∣_; prod; sum)
import Data.Nat.Properties as ℕₚ
open import Data.List.Membership.DecSetoid ℕₚ.≡-decSetoid using (_∈?_)

open import Utils using (Runner; mkRunner; module Utils)
open Utils.Expression using (Exp-ℕ; Exp-from-String')
open Utils.Parser using (parse-ℕ; generic-parser-by-lines)
open import Utils.WithK using (Exp-star-map)

-- Data

Parsed : Set
Parsed = List⁺ (List ℕ × List ℕ)

example-input : String
example-input = "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53\nCard 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19\nCard 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1\nCard 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83\nCard 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36\nCard 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11"

example-parsed : Parsed
example-parsed = ( (41 ∷ 48 ∷ 83 ∷ 86 ∷ 17 ∷ []) 
                 , (83 ∷ 86 ∷ 6 ∷ 31 ∷ 17 ∷ 9 ∷ 48 ∷ 53 ∷ []))
              ∷⁺ ( (13 ∷ 32 ∷ 20 ∷ 16 ∷ 61 ∷ []) 
                 , (61 ∷ 30 ∷ 68 ∷ 82 ∷ 17 ∷ 32 ∷ 24 ∷ 19 ∷ []))
              ∷⁺ ( (1 ∷ 21 ∷ 53 ∷ 59 ∷ 44 ∷ []) 
                 , (69 ∷ 82 ∷ 63 ∷ 72 ∷ 16 ∷ 21 ∷ 14 ∷ 1 ∷ []))
              ∷⁺ ( (41 ∷ 92 ∷ 73 ∷ 84 ∷ 69 ∷ []) 
                 , (59 ∷ 84 ∷ 76 ∷ 51 ∷ 58 ∷ 5 ∷ 54 ∷ 83 ∷ []))
              ∷⁺ ( (87 ∷ 83 ∷ 26 ∷ 28 ∷ 32 ∷ []) 
                 , (88 ∷ 30 ∷ 70 ∷ 12 ∷ 93 ∷ 22 ∷ 82 ∷ 36 ∷ []))
            ∷⁺ [ ( (31 ∷ 18 ∷ 13 ∷ 56 ∷ 72 ∷ []) 
                 , (74 ∷ 77 ∷ 10 ∷ 23 ∷ 35 ∷ 67 ∷ 36 ∷ 11 ∷ [])) ]⁺

example-output1 : ℕ
example-output1 = 13

example-output2 : ℕ
example-output2 = 30

-- Parse

valid-number : Exp
valid-number = (((singleton ' ') ⋆) ∙ (singleton ' ')) ∙ Exp-ℕ

valid-line : Exp
valid-line = (Exp-from-String' "Card")
           ∙ valid-number
           ∙ (singleton ':')
           ∙ (valid-number ⋆)
           ∙ (Exp-from-String' " |")
           ∙ (valid-number ⋆)

parse-number : ∀ {s} → (s ∈ valid-number) → ℕ
parse-number (prod _ _ n) = parse-ℕ n

parse-line : ∀ {s} → (s ∈ valid-line) → List ℕ × List ℕ
parse-line (prod _ _ (prod _ _ (prod _ _ (prod _ ns (prod _ _ ms))))) = parse-numbers ns , parse-numbers ms
  where
    parse-numbers : ∀ {s} → (s ∈ (valid-number ⋆)) → List ℕ
    parse-numbers = Exp-star-map parse-number

parse-input : String → Maybe Parsed
parse-input = generic-parser-by-lines valid-line parse-line

_ : parse-input example-input ≡ just example-parsed
_ = refl

-- Solvers

winning : (List ℕ × List ℕ) → List ℕ
winning (ws , ys) = List.filter (λ w → w ∈? ys) ws

solve1 : String → Maybe ℕ
solve1 = Maybe.map (Utils.List⁺-sum ∘ List⁺.map (points ∘ winning)) ∘ parse-input
  where
    points : List ℕ → ℕ
    points = (λ n → if n ℕ.≡ᵇ 0 then 0 else 2 ^ (n ∸ 1)) ∘ (List.length)

solve2 : String → Maybe ℕ
solve2 = Maybe.map (cards-to-instances) ∘ parse-input
  where
    suum : List ℕ → List ℕ → List ℕ
    suum [] ys = ys
    suum xs [] = xs
    suum (x ∷ xs) (y ∷ ys) = (x + y) ∷ (suum xs ys)

    const : ℕ → ℕ → List ℕ
    const M n = List.applyUpTo (λ _ → n) M

    aa : ℕ → (List ℕ) × (List ℕ) → (List ℕ) × (List ℕ)
    aa 0 (ss , []) = 1 ∷ ss , []
    aa 0 (ss , (r ∷ rs)) = (r + 1) ∷ ss , rs
    aa w (ss , []) = 1 ∷ ss , const w 1
    aa w (ss , (r ∷ rs)) = (r + 1) ∷ ss , suum rs (const w (r + 1))

    price' : List ℕ → (List ℕ) × (List ℕ)
    price' = List.foldr aa ([] , [])

    price : List ℕ → List ℕ
    price = proj₁ ∘ price' ∘ List.reverse

    cards-to-instances : List⁺ (List ℕ × List ℕ) → ℕ
    cards-to-instances = List.sum ∘ price ∘ List⁺.toList ∘ List⁺.map (List.length ∘ winning)

_ : solve1 example-input ≡ just example-output1
_ = refl

_ : solve2 example-input ≡ just example-output2
_ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day04" "Day 04"
     