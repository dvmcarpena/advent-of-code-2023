{-# OPTIONS --with-K --safe #-}

module Day03 where

-- Imports

open import Function.Base using (_∘_; _$_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
open import Data.Nat as ℕ using (ℕ; _+_; _≤ᵇ_)
open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)
open import Data.String as String using (String)
import Data.Char.Properties as Charₚ
open import Text.Regex Charₚ.≤-decPoset using (Exp; _∈?_; _∈_; singleton; _⋆; _∙_; _∣_; prod; sum)

open import utils as Utils using (Runner; mkRunner; module Utils)
open Utils.Expression using (Exp-ℕ; Exp-from-Strings')
open Utils.Parser using (parse-ℕ; generic-parser-by-lines)
open import utils-with-k using (Exp-star-fold)

-- Data

Parsed : Set
Parsed = (List (ℕ × ℕ)) × (List (ℕ × ℕ × ℕ × ℕ))

example-input : String
example-input = "467..114..\n...*......\n..35..633.\n......#...\n617*......\n.....+.58.\n..592.....\n......755.\n...$.*....\n.664.598.."

example-parsed : Parsed
example-parsed = ((2 , 4) ∷ (4 , 7) ∷ (5 , 4) ∷ (6 , 6) ∷ (9 , 4) ∷ (9 , 6) ∷ []) 
               , ((467 , 1  , 1 , 3) ∷ 
                  (114 , 1  , 6 , 3) ∷ 
                  (35  , 3  , 3 , 2) ∷ 
                  (633 , 3  , 7 , 3) ∷ 
                  (617 , 5  , 1 , 3) ∷ 
                  (58  , 6  , 8 , 2) ∷ 
                  (592 , 7  , 3 , 3) ∷ 
                  (755 , 8  , 7 , 3) ∷ 
                  (664 , 10 , 2 , 3) ∷ 
                  (598 , 10 , 6 , 3) ∷ [])

example-output1 : ℕ
example-output1 = 4361

-- example-output2 : ℕ
-- example-output2 = ?

-- Parse

Exp-dot : Exp
Exp-dot = singleton '.'

Exp-symbol : Exp
Exp-symbol = Exp-from-Strings' ("*" ∷ "#" ∷ "+" ∷ "$" ∷ "=" ∷ "-" ∷ "@" ∷ "%" ∷ "/" ∷ "&" ∷ []) 

valid-info : Exp
valid-info = Exp-ℕ ∣ Exp-symbol

valid-line : Exp
valid-line = (Exp-dot ⋆) ∙ ((valid-info ∙ (Exp-dot ⋆)) ⋆)

_ : True ((String.toList "467..*..114..") ∈? valid-line)
_ = _

parse-info : ∀ {s} → ℕ → (s ∈ (valid-info ∙ (Exp-dot ⋆))) → ℕ × (ℕ ⊎ (ℕ × ℕ × ℕ))
parse-info i (prod {l} {d} _ (sum (inj₁ n)) _) = i + (List.length d) + (List.length l) , inj₂ (parse-ℕ n , i + 1 , List.length l)
parse-info i (prod {_} {d} _ (sum (inj₂ y)) _) = i + (List.length d) + 1 , inj₁ (i + 1)

parse-line : ∀ {s} → (s ∈ valid-line) → (List ℕ) × (List (ℕ × ℕ × ℕ))
parse-line (prod {d} _ _ s) = format $ Exp-star-fold parse-info (List.length d) s
  where
    format : List (ℕ ⊎ (ℕ × ℕ × ℕ)) → (List ℕ) × (List (ℕ × ℕ × ℕ))
    format [] = [] , []
    format ((inj₁ n) ∷ ps) = (λ (ns , nms) → (n ∷ ns) , nms) $ format ps
    format ((inj₂ (n , m , l)) ∷ ps) = (λ (ns , nms) → ns , (n , m , l) ∷ nms) $ format ps

parse-input : String → Maybe Parsed
parse-input = Maybe.map (join-rows ∘ List⁺.toList) ∘ generic-parser-by-lines valid-line parse-line
    where
        add-row : (ℕ × (List ℕ) × (List (ℕ × ℕ × ℕ))) → (List (ℕ × ℕ)) × (List (ℕ × ℕ × ℕ × ℕ))
        add-row (r , ss , ns) = List.map (λ c → (r + 1 , c)) ss , List.map (λ (n , c , l) → (n , r + 1 , c , l)) ns

        join-rows : List ((List ℕ) × (List (ℕ × ℕ × ℕ))) → Parsed
        join-rows = Utils.Prod-List-concat ∘ List.map add-row ∘ Utils.enumerate

_ : parse-input example-input ≡ just example-parsed
_ = refl

-- Solvers

solve1 : String → Maybe ℕ
solve1 = Maybe.map (solve)  ∘ parse-input
  where
    expand : (ℕ × ℕ × ℕ × ℕ) → ℕ × (List (ℕ × ℕ))
    expand (n , r , c , l) = n , (List.map (λ d → r , c + d) $ List.downFrom l)

    is-part : List (ℕ × ℕ) → (ℕ × (List (ℕ × ℕ))) → Bool
    is-part ss (_ , ns) = List.foldr (λ s b → (adjacent-symbol s) ∨ b) false ss
      where
        number-adjacent-symbol : (ℕ × ℕ) → (ℕ × ℕ) → Bool
        number-adjacent-symbol (sr , sc) (nr , nc) = ((nr ≤ᵇ sr + 1) ∧ (sr ≤ᵇ nr + 1)) 
                                                   ∧ ((nc ≤ᵇ sc + 1) ∧ (sc ≤ᵇ nc + 1))
        
        adjacent-symbol : (ℕ × ℕ) → Bool
        adjacent-symbol s = List.foldl (λ b n → (number-adjacent-symbol s n) ∨ b) false ns

    filter-parts : (List (ℕ × ℕ)) × (List (ℕ × (List (ℕ × ℕ)))) → List ℕ    
    filter-parts (ss , ns) = List.map proj₁ $ List.boolFilter (is-part ss) ns 

    solve : Parsed → ℕ
    solve = List.sum ∘ filter-parts ∘ Product.map₂ (List.map expand)

solve2 : String → Maybe ℕ
solve2 = Maybe.map (solve)  ∘ parse-input
  where
    solve : Parsed → ℕ
    solve x = 0

_ : solve1 example-input ≡ just example-output1
_ = refl

-- _ : solve2 example-input ≡ just example-output2
-- _ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day03" "Day 03"
