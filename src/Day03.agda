{-# OPTIONS --cubical-compatible --safe #-}

module Day03 where

-- Imports

open import Function.Base using (_∘_; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Char as Char using (Char)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_) renaming ([_] to [_]⁺)
open import Data.Nat as ℕ using (ℕ; _+_; _≤ᵇ_; _*_)
open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)
open import Data.String as String using (String)

open import Utils using (Runner; mkRunner; module Utils)

-- Data

Parsed : Set
Parsed = (List (Char × ℕ × ℕ)) × (List (ℕ × ℕ × ℕ × ℕ))

example-input : String
example-input = "467..114..\n...*......\n..35..633.\n......#...\n617*......\n.....+.58.\n..592.....\n......755.\n...$.*....\n.664.598.."

example-parsed : Parsed
example-parsed = (('*' , 2 , 4) ∷ 
                  ('#' , 4 , 7) ∷ 
                  ('*' , 5 , 4) ∷ 
                  ('+' , 6 , 6) ∷ 
                  ('$' , 9 , 4) ∷ 
                  ('*' , 9 , 6) ∷ []) 
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

example-output2 : ℕ
example-output2 = 467835

-- Parse

parse-input : String → Maybe Parsed
parse-input = Utils.Maybe-idempotent ∘ Maybe.map (Maybe.map join-rows ∘ aa ∘ List⁺.toList) ∘ List⁺.fromList ∘ String.lines
  where
    format : List ((Char × ℕ) ⊎ (Maybe (ℕ × ℕ × ℕ))) → (List (Char × ℕ)) × (List (Maybe (ℕ × ℕ × ℕ)))
    format [] = [] , []
    format ((inj₁ n) ∷ ps) = (λ (ns , nms) → (n ∷ ns) , nms) $ format ps
    format ((inj₂ a) ∷ ps) = (λ (ns , nms) → ns , a ∷ nms) $ format ps

    ff : ℕ × (List Char) → Maybe (ℕ × ℕ × ℕ)
    ff (c , cs) with ℕ-readMaybe 10 (String.fromList cs)
    ... | nothing = nothing
    ... | just n = just (n , c , List.length cs)

    ee : Maybe (ℕ × (List Char)) → List ((Char × ℕ) ⊎ (ℕ × Char)) → List ((Char × ℕ) ⊎ (ℕ × (List Char)))
    ee nothing [] = []
    ee (just a) [] = (inj₂ a) ∷ []
    ee nothing ((inj₁ n) ∷ xs) = (inj₁ n) ∷ (ee nothing xs)
    ee (just a) ((inj₁ n) ∷ xs) = (inj₂ a) ∷ (inj₁ n) ∷ (ee nothing xs)
    ee nothing ((inj₂ (n , c)) ∷ xs) = ee (just (n , c ∷ [])) xs
    ee (just (n' , cs)) ((inj₂ (n , c)) ∷ xs) = if n ℕ.≡ᵇ (n' + List.length cs) then (ee (just (n' , cs List.++ (c ∷ []))) xs) else ((inj₂ (n' , cs)) ∷ (ee (just (n , c ∷ [])) xs))

    isSymbol : Char → Bool
    isSymbol c = (c Char.== '*') ∨ (c Char.== '#') ∨ (c Char.== '+') ∨ (c Char.== '$') ∨ (c Char.== '=') ∨ (c Char.== '-') ∨ (c Char.== '@') ∨ (c Char.== '%') ∨ (c Char.== '/') ∨ (c Char.== '&')
    
    dd : ℕ × Char → Maybe ((Char × ℕ) ⊎ (ℕ × Char))
    dd (n , c) = if (Char.isDigit c) then (just (inj₂ (n + 1 , c))) else if isSymbol c then (just (inj₁ (c , n + 1))) else nothing

    ol : (List (Char × ℕ)) × (List (Maybe (ℕ × ℕ × ℕ))) → Maybe ((List (Char × ℕ)) × (List (ℕ × ℕ × ℕ)))
    ol (a , []) = just (a , [])
    ol (a , (nothing ∷ xs)) = nothing
    ol (a , ((just x) ∷ xs)) with (ol (a , xs))
    ... | nothing = nothing
    ... | (just (_ , v)) = just (a , (x ∷ v))

    bb : String → Maybe ((List (Char × ℕ)) × (List (ℕ × ℕ × ℕ)))
    bb = Utils.Maybe-idempotent ∘ Maybe.map (ol ∘ format ∘ List.map (Sum.map₂ ff) ∘ (ee nothing)) ∘ Utils.List-propagate-maybe ∘ List.map dd ∘ List.boolFilter ((λ (n , c) → not (c Char.== '.'))) ∘ Utils.enumerate ∘ String.toList

    aa : List String → Maybe (List ((List (Char × ℕ)) × (List (ℕ × ℕ × ℕ))))
    aa = Utils.List-propagate-maybe ∘ List.map bb

    add-row : (ℕ × (List (Char × ℕ)) × (List (ℕ × ℕ × ℕ))) → (List (Char × ℕ × ℕ)) × (List (ℕ × ℕ × ℕ × ℕ))
    add-row (r , ss , ns) = List.map (λ (s , c) → (s , r + 1 , c)) ss , List.map (λ (n , c , l) → (n , r + 1 , c , l)) ns

    join-rows : List ((List (Char × ℕ)) × (List (ℕ × ℕ × ℕ))) → Parsed
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
    solve = List.sum ∘ filter-parts ∘ Product.map₂ (List.map expand) ∘ Product.map₁ (List.map proj₂)

solve2 : String → Maybe ℕ
solve2 = Maybe.map (solve)  ∘ parse-input
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
    
    find-gears : (List (ℕ × ℕ)) × (List (ℕ × (List (ℕ × ℕ)))) → List (List ℕ)
    find-gears (ss , ns) = List.map lola ss
      where
        number-adjacent-symbol : (ℕ × ℕ) → (ℕ × ℕ) → Bool
        number-adjacent-symbol (sr , sc) (nr , nc) = ((nr ≤ᵇ sr + 1) ∧ (sr ≤ᵇ nr + 1)) 
                                                   ∧ ((nc ≤ᵇ sc + 1) ∧ (sc ≤ᵇ nc + 1))
        
        adjacent-symbol : (ℕ × ℕ) → (ℕ × (List (ℕ × ℕ))) → Bool
        adjacent-symbol s (_ , ns) = List.foldl (λ b n → (number-adjacent-symbol s n) ∨ b) false ns

        lola : ℕ × ℕ → List ℕ
        lola p = List.map proj₁ $ List.boolFilter (adjacent-symbol p) ns

    filter-true-gears : List ℕ → Maybe (ℕ × ℕ)
    filter-true-gears [] = nothing
    filter-true-gears (_ ∷ []) = nothing
    filter-true-gears (x ∷ y ∷ []) = just (x , y)
    filter-true-gears _ = nothing

    aaat : List (Maybe (ℕ × ℕ)) → List (ℕ × ℕ)
    aaat [] = []
    aaat (nothing ∷ xs) = aaat xs
    aaat ((just p) ∷ xs) = p ∷ (aaat xs)

    aa : (List (ℕ × ℕ)) × (List (ℕ × (List (ℕ × ℕ)))) → List (ℕ × ℕ)    
    aa = aaat ∘ List.map filter-true-gears ∘ find-gears

    is-gear : Char × ℕ × ℕ → Bool
    is-gear (c , _ , _) = c Char.== '*'

    solve : Parsed → ℕ
    solve = List.sum ∘ List.map (λ (n , m) → n * m) ∘ aa ∘ Product.map₂ (List.map expand) ∘ Product.map₁ (List.map proj₂ ∘ List.boolFilter is-gear)

_ : solve1 example-input ≡ just example-output1
_ = refl

_ : solve2 example-input ≡ just example-output2
_ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day03" "Day 03"
  