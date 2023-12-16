{-# OPTIONS --with-K --safe #-}

module Day05 where

-- Imports

open import Function.Base using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; False; from-yes)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool as Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Char as Char using (Char)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
open import Data.Nat as ℕ using (ℕ; suc; _+_; _∸_; _*_; _^_; _<?_; _<ᵇ_; _≤ᵇ_; _<_)
open import Data.Nat.Show using (toDecimalChars) renaming (show to ℕ-show)
open import Data.String as String using (String)
import Data.Char.Properties as Charₚ
open import Relation.Binary using (DecPoset)
import Text.Regex.Base (DecPoset.preorder Charₚ.≤-decPoset) as Regex
open import Text.Regex Charₚ.≤-decPoset using (Exp; _∈_; _∈?_; singleton; _⋆; _∙_; _∣_; prod; sum)
import Data.Nat.Properties as ℕₚ
open import Data.Vec as Vec using (Vec; _∷_; [])

open import Utils using (Runner; mkRunner; module Utils)
open Utils.Expression using (Exp-ℕ; Exp-from-String')
open Utils.Parser using (parse-ℕ; generic-parser)
open import Utils.WithK using (Exp-star-map; Exp-prod-map₁; Exp-prod-map₂; Exp-prod-map)

open import Utils using (Runner; mkRunner; module Utils)

-- Data

Parsed : Set
Parsed = List ℕ × Vec (List (ℕ × ℕ × ℕ)) 7

example-input : String
example-input = "seeds: 79 14 55 13\n\nseed-to-soil map:\n50 98 2\n52 50 48\n\nsoil-to-fertilizer map:\n0 15 37\n37 52 2\n39 0 15\n\nfertilizer-to-water map:\n49 53 8\n0 11 42\n42 0 7\n57 7 4\n\nwater-to-light map:\n88 18 7\n18 25 70\n\nlight-to-temperature map:\n45 77 23\n81 45 19\n68 64 13\n\ntemperature-to-humidity map:\n0 69 1\n1 0 69\n\nhumidity-to-location map:\n60 56 37\n56 93 4\n"

example-parsed : Parsed
example-parsed = (79 ∷ 14 ∷ 55 ∷ 13 ∷ []) 
               , ( ((50 , 98 ,  2) ∷ (52 , 50 , 48) ∷ [])
                 ∷ (( 0 , 15 , 37) ∷ (37 , 52 ,  2) ∷ (39 ,  0 , 15) ∷ [])
                 ∷ ((49 , 53 ,  8) ∷ ( 0 , 11 , 42) ∷ (42 ,  0 ,  7) ∷ (57 ,  7 ,  4) ∷ [])
                 ∷ ((88 , 18 ,  7) ∷ (18 , 25 , 70) ∷ [])
                 ∷ ((45 , 77 , 23) ∷ (81 , 45 , 19) ∷ (68 , 64 , 13) ∷ [])
                 ∷ (( 0 , 69 ,  1) ∷ ( 1 ,  0 , 69) ∷ [])
                 ∷ ((60 , 56 , 37) ∷ (56 , 93 ,  4) ∷ [])
                 ∷ [])

example-output1 : ℕ
example-output1 = 35

example-output2 : ℕ
example-output2 = 0

-- Parse

valid-seeds : Exp
valid-seeds = (Exp-from-String' "seeds:") ∙ (((singleton ' ') ∙ Exp-ℕ) ⋆) ∙ (singleton '\n')

valid-map : Exp
valid-map = Exp-ℕ ∙ (singleton ' ') ∙ Exp-ℕ ∙ (singleton ' ') ∙ Exp-ℕ ∙ (singleton '\n')

valid-maps : Exp
valid-maps = ((Exp-from-String' "\nseed-to-soil map:\n") ∙ (valid-map ⋆))
           ∙ ((Exp-from-String' "\nsoil-to-fertilizer map:\n") ∙ (valid-map ⋆))
           ∙ ((Exp-from-String' "\nfertilizer-to-water map:\n") ∙ (valid-map ⋆))
           ∙ ((Exp-from-String' "\nwater-to-light map:\n") ∙ (valid-map ⋆))
           ∙ ((Exp-from-String' "\nlight-to-temperature map:\n") ∙ (valid-map ⋆))
           ∙ ((Exp-from-String' "\ntemperature-to-humidity map:\n") ∙ (valid-map ⋆))
           ∙ ((Exp-from-String' "\nhumidity-to-location map:\n") ∙ (valid-map ⋆))

valid-content : Exp
valid-content = valid-seeds ∙ valid-maps

parse-content : ∀ {s} → (s ∈ valid-content) → List ℕ × Vec (List (ℕ × ℕ × ℕ)) 7
parse-content (prod _ s ms) = parse-seeds s , parse-maps ms
  where
    parse-seeds : ∀ {s} → (s ∈ valid-seeds) → List ℕ
    parse-seeds (prod _ _ (prod _ ns _)) = Exp-star-map (Exp-prod-map₂ parse-ℕ) ns

    parse-map : ∀ {s} → (s ∈ valid-map) → ℕ × ℕ × ℕ
    parse-map (prod _ n₁ (prod _ _ (prod _ n₂ (prod _ _ (prod _ n₃ _))))) = parse-ℕ n₁ , parse-ℕ n₂ , parse-ℕ n₃

    parse-full-map : ∀ {s e} → (s ∈ (e Regex.∙ (valid-map Regex.⋆))) → List (ℕ × ℕ × ℕ)
    parse-full-map = Exp-prod-map₂ (Exp-star-map parse-map)

    parse-maps : ∀ {s} → (s ∈ valid-maps) → Vec (List (ℕ × ℕ × ℕ)) 7
    -- parse-maps (prod _ m₁ (prod _ m₂ (prod _ m₃ (prod _ m₄ (prod _ m₅ (prod _ m₆ m₇)))))) = ((lol m₁) ∷ (lol m₂) ∷ (lol m₃) ∷ (lol m₄) ∷ (lol m₅) ∷ (lol m₆) ∷ (lol m₇) ∷ [])
    parse-maps a = m₁ ∷ m₂ ∷ m₃ ∷ m₄ ∷ m₅ ∷ m₆ ∷ m₇ ∷ []
      where
        m₁ = Exp-prod-map₁ parse-full-map a
        m₂ = Exp-prod-map₂ (Exp-prod-map₁ parse-full-map) a
        m₃ = Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₁ parse-full-map)) a
        m₄ = Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₁ parse-full-map))) a
        m₅ = Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₁ parse-full-map)))) a
        m₆ = Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₁ parse-full-map))))) a
        m₇ = Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ (Exp-prod-map₂ parse-full-map))))) a

parse-input : String → Maybe Parsed
parse-input = generic-parser valid-content parse-content

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

-- _ : solve1 example-input ≡ just example-output1
-- _ = refl

-- _ : solve2 example-input ≡ just example-output2
-- _ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day05" "Day 05"
    