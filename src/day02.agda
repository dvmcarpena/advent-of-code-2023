{-# OPTIONS --with-K --safe #-}

module day02 where

-- Imports

open import Function.Base using (_$_; _∘_; id)
open import Data.Product using (_×_; _,_; <_,_>)
open import Data.Sum as Sum using (_⊎_)
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
open import Text.Regex Charₚ.≤-decPoset

open import utils using (EnrichedRunner; List⁺-propagate-maybe; Maybe-idempotent; duplicate; Exp-reverse; Exp-from-String')

-- Data

Output : Set
Output = ℕ

Output-show : Output → String
Output-show = ℕ-show

example-input : String
example-input = "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green\nGame 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue\nGame 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red\nGame 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red\nGame 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"

example-parsed : List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ)))
example-parsed = (1 , ((4 , (0 , 3)) ∷⁺ (1 , (2 , 6)) ∷⁺ List⁺.[ (0 , (2 , 0)) ])) 
  ∷⁺ (2 , ((0 , (2 , 1)) ∷⁺ (1 , (3 , 4)) ∷⁺ List⁺.[ (0 , (1 , 1)) ])) 
  ∷⁺ (3 , ((20 , (8 , 6)) ∷⁺ (4 , (13 , 5)) ∷⁺ List⁺.[ (1 , (5 , 0)) ])) 
  ∷⁺ (4 , ((3 , (1 , 6)) ∷⁺ (6 , (3 , 0)) ∷⁺ List⁺.[ (14 , (3 , 15)) ])) 
  ∷⁺ List⁺.[ (5 , ((6 , (3 , 1)) ∷⁺ List⁺.[ (1 , (2 , 2)) ])) ]

example-output1 : ℕ
example-output1 = 8

example-output2 : ℕ
example-output2 = 2286

-- Parse

Exp-ℕ : Exp
Exp-ℕ = [ '1' ─ '9' ∷ [] ] ∙ [ '0' ─ '9' ∷ [] ] ⋆

Exp-red : Exp
Exp-red = Exp-from-String' " red"

Exp-green : Exp
Exp-green = Exp-from-String' " green"

Exp-blue : Exp
Exp-blue = Exp-from-String' " blue"

Exp-sep : Exp
Exp-sep = Exp-from-String' ", "

valid-1-set : Exp
valid-1-set = (Exp-ℕ ∙ Exp-red) ∣ (Exp-ℕ ∙ Exp-green) ∣ (Exp-ℕ ∙ Exp-blue)

valid-2-set : Exp
valid-2-set = (Exp-ℕ ∙ Exp-red ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-green)
            ∣ (Exp-ℕ ∙ Exp-red ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-blue)
            ∣ (Exp-ℕ ∙ Exp-green ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-red)
            ∣ (Exp-ℕ ∙ Exp-green ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-blue)
            ∣ (Exp-ℕ ∙ Exp-blue ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-red)
            ∣ (Exp-ℕ ∙ Exp-blue ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-green)

valid-3-set : Exp
valid-3-set = (Exp-ℕ ∙ Exp-red ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-green ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-blue)
            ∣ (Exp-ℕ ∙ Exp-red ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-blue ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-green)
            ∣ (Exp-ℕ ∙ Exp-green ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-red ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-blue)
            ∣ (Exp-ℕ ∙ Exp-green ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-blue ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-red)
            ∣ (Exp-ℕ ∙ Exp-blue ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-red ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-green)
            ∣ (Exp-ℕ ∙ Exp-blue ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-green ∙ Exp-sep ∙ Exp-ℕ ∙ Exp-red)

valid-set : Exp
valid-set = valid-1-set ∣ valid-2-set ∣ valid-3-set

valid-sets : Exp
valid-sets = ((valid-set ∙ (Exp-from-String' "; ")) ⋆) ∙ valid-set

valid-line : Exp
valid-line = (Exp-from-String' "Game ") 
           ∙ Exp-ℕ 
           ∙ (Exp-from-String' ": ") 
           ∙ valid-sets

_ : True ((String.toList "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green") ∈? valid-line)
_ = _

parse-nat : ∀ {s} → (s ∈ Exp-ℕ) → ℕ
parse-nat {s} _ = convert $ List.map (λ c → (Char.toℕ c) ∸ (Char.toℕ '0')) s
  where
    convert : List ℕ → ℕ
    convert = List.foldl (λ acc d → 10 * acc + d) 0

parse-1-set : ∀ {s} → (s ∈ valid-1-set) → ℕ × ℕ × ℕ
parse-1-set (sum (inj₁ (prod _ n _))) = (parse-nat n , 0 , 0)
parse-1-set (sum (inj₂ (sum (inj₁ (prod _ n _))))) = (0 , parse-nat n , 0)
parse-1-set (sum (inj₂ (sum (inj₂ (prod _ n _))))) = (0 , 0 , parse-nat n)

parse-nat-2-set : ∀ {s e1 e2} → (s ∈ (Exp-ℕ Regex.∙ e1 Regex.∙ Exp-sep Regex.∙ Exp-ℕ Regex.∙ e2)) → ℕ × ℕ
parse-nat-2-set (prod _ n1 (prod _ _ (prod _ _ (prod _ n2 _)))) = Product.map parse-nat parse-nat (n1 , n2)

parse-nat-3-set : ∀ {s e1 e2 e3} → (s ∈ (Exp-ℕ Regex.∙ e1 Regex.∙ Exp-sep Regex.∙ Exp-ℕ Regex.∙ e2 Regex.∙ Exp-sep Regex.∙ Exp-ℕ Regex.∙ e3)) → ℕ × ℕ × ℕ
parse-nat-3-set (prod _ n1 (prod _ _ (prod _ _ (prod _ n2 (prod _ _ (prod _ _ (prod _ n3 _))))))) = (parse-nat n1 , parse-nat n2 , parse-nat n3)

parse-6-cases : ∀ {s e1 e2 e3 e4 e5 e6} 
  → {A : Set}
  → ((x : (s ∈ e1) ⊎ (s ∈ e2) ⊎ (s ∈ e3) ⊎ (s ∈ e4) ⊎ (s ∈ e5) ⊎ (s ∈ e6)) → A)
  → (s ∈ (e1 Regex.∣ e2 Regex.∣ e3 Regex.∣ e4 Regex.∣ e5 Regex.∣ e6))
  → A
parse-6-cases f (sum (inj₁ x)) = f (inj₁ x)
parse-6-cases f (sum (inj₂ (sum (inj₁ x)))) = f (inj₂ (inj₁ x))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₁ x)))))) = f (inj₂ (inj₂ (inj₁ x)))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₁ x)))))))) = f (inj₂ (inj₂ (inj₂ (inj₁ x))))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₁ x)))))))))) = f (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₂ x)))))))))) = f (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))

Exp-star-elimination : ∀ {s e} → {A : Set} → (∀ {t} → (t ∈ e) → A) → (s ∈ (e Regex.⋆)) → List (A)
Exp-star-elimination f (star (sum (inj₁ _))) = []
Exp-star-elimination f (star (sum (inj₂ (prod _ p1 r)))) = (f p1) ∷ (Exp-star-elimination f r)

parse-2-set : ∀ {s} → (s ∈ valid-2-set) → ℕ × ℕ × ℕ
parse-2-set = parse-6-cases Sum.[ f1 , Sum.[ f2 , Sum.[ f3 , Sum.[ f4 , Sum.[ f5 , f6 ] ] ] ] ]
  where
    f1 = (λ (n1 , n2) → (n1 , n2 , 0 )) ∘ parse-nat-2-set
    f2 = (λ (n1 , n2) → (n1 , 0  , n2)) ∘ parse-nat-2-set
    f3 = (λ (n1 , n2) → (n2 , n1 , 0 )) ∘ parse-nat-2-set
    f4 = (λ (n1 , n2) → (0  , n1 , n2)) ∘ parse-nat-2-set
    f5 = (λ (n1 , n2) → (n2 , 0  , n1)) ∘ parse-nat-2-set
    f6 = (λ (n1 , n2) → (0  , n2 , n1)) ∘ parse-nat-2-set

parse-3-set : ∀ {s} → (s ∈ valid-3-set) → ℕ × ℕ × ℕ
parse-3-set = parse-6-cases Sum.[ f1 , Sum.[ f2 , Sum.[ f3 , Sum.[ f4 , Sum.[ f5 , f6 ] ] ] ] ]
  where
    f1 = (λ (n1 , n2 , n3) → (n1 , n2 , n3)) ∘ parse-nat-3-set
    f2 = (λ (n1 , n2 , n3) → (n1 , n3 , n2)) ∘ parse-nat-3-set
    f3 = (λ (n1 , n2 , n3) → (n2 , n1 , n3)) ∘ parse-nat-3-set
    f4 = (λ (n1 , n2 , n3) → (n3 , n1 , n2)) ∘ parse-nat-3-set
    f5 = (λ (n1 , n2 , n3) → (n2 , n3 , n1)) ∘ parse-nat-3-set
    f6 = (λ (n1 , n2 , n3) → (n3 , n2 , n1)) ∘ parse-nat-3-set

parse-set : ∀ {s} → (s ∈ valid-set) → ℕ × ℕ × ℕ
parse-set (sum (inj₁ x)) = parse-1-set x
parse-set (sum (inj₂ (sum (inj₁ x)))) = parse-2-set x
parse-set (sum (inj₂ (sum (inj₂ x)))) = parse-3-set x

parse-sets : ∀ {s} → (s ∈ valid-sets) → List⁺ (ℕ × ℕ × ℕ)
parse-sets (prod _ st s1) = (Exp-star-elimination f st) List⁺.++⁺ List⁺.[ (parse-set s1) ]
  where
    f : ∀ {s} → (s ∈ (valid-set ∙ (Exp-from-String' "; "))) → ℕ × ℕ × ℕ
    f (prod _ s _) = parse-set s



parse-line : ∀ {s} → (s ∈ valid-line) → ℕ × (List⁺ (ℕ × ℕ × ℕ))
parse-line (prod _ _ (prod {n} {_} {_} _ n-is-nat (prod _ _ sets))) = (parse-nat n-is-nat , parse-sets sets)

regex : Regex
regex = record
  { fromStart  = true
  ; tillEnd    = true
  ; expression = valid-line
  }

generic-parser-by-lines : (Parsed : Set)
  → (r : Regex) 
  → (∀ {s} → (s ∈ (Regex.expression r)) → Parsed) 
  → String
  → Maybe (List⁺ Parsed)
generic-parser-by-lines Parsed r to-Parsed = Maybe-idempotent ∘ Maybe.map generic-parse-lines ∘ List⁺.fromList ∘ String.lines
  where
    generic-parse-line : List Char → Maybe (Parsed)
    generic-parse-line s = Maybe.map (to-Parsed ∘ Match.match) $ Maybe.decToMaybe $ search s r

    generic-parse-lines : List⁺ String → Maybe (List⁺ (Parsed))
    generic-parse-lines = List⁺-propagate-maybe ∘ List⁺.map (generic-parse-line ∘ String.toList)

parse-input : String → Maybe (List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ))))
parse-input = generic-parser-by-lines (ℕ × (List⁺ (ℕ × ℕ × ℕ))) regex parse-line

_ : parse-input example-input ≡ just example-parsed
_ = refl

-- Solvers

solve1 : String → Maybe Output
solve1 = Maybe.map (solve)  ∘ parse-input
  where
    solve : List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ))) → ℕ
    solve = List.sum ∘ List.map proj₁ ∘ List.boolFilter f ∘ List⁺.toList
      where
        gg : ℕ × ℕ × ℕ → Bool
        gg (r , (g , b)) = (r ≤ᵇ 12) ∧ (g ≤ᵇ 13) ∧ (b ≤ᵇ 14)
        
        f : ℕ × (List⁺ (ℕ × ℕ × ℕ)) → Bool
        f (_ , xs) = List.all gg (List⁺.toList xs)

solve2 : String → Maybe Output
solve2 = Maybe.map (solve)  ∘ parse-input
  where
    max : List (ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ
    max = rec-max (0 , 0 , 0)
      where
        rec-max : (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ
        rec-max p [] = p 
        rec-max (m1 , m2 , m3) ((n1 , n2 , n3) ∷ ns) = rec-max ((if n1 ≤ᵇ m1 then m1 else n1) , (if n2 ≤ᵇ m2 then m2 else n2) , (if n3 ≤ᵇ m3 then m3 else n3)) ns 

    product : ℕ × ℕ × ℕ → ℕ
    product (n1 , n2 , n3) = n1 * n2 * n3

    solve : List⁺ (ℕ × (List⁺ (ℕ × ℕ × ℕ))) → ℕ
    solve = List.sum ∘ List⁺.toList ∘ List⁺.map (product ∘ max ∘ List⁺.toList ∘ proj₂)

_ : solve1 example-input ≡ just example-output1
_ = refl

_ : solve2 example-input ≡ just example-output2
_ = refl

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
     