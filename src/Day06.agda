{-# OPTIONS --with-K --safe #-}

module Day06 where

-- Imports

open import Function.Base using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
open import Text.Regex Charₚ.≤-decPoset using (Exp; _∈_; singleton; _⋆; _∙_; _∣_; prod; sum)
import Data.Nat.Properties as ℕₚ
open import Data.List.Membership.DecSetoid ℕₚ.≡-decSetoid using (_∈?_)

open import Utils using (Runner; mkRunner; module Utils)
open Utils.Expression using (Exp-ℕ; Exp-from-String')
open Utils.Parser using (parse-ℕ; generic-parser)
open import Utils.WithK using (Exp-star-map)

open import Utils using (Runner; mkRunner; module Utils)

-- Data

Parsed : Set
Parsed = List (ℕ × ℕ)

example-input : String
example-input = "Time:      7  15   30\nDistance:  9  40  200"

example-parsed : Parsed
example-parsed = List⁺.toList ((7 , 9) ∷⁺ (15 , 40) ∷⁺ [ (30 , 200) ]⁺)

example-output1 : ℕ
example-output1 = 288

example-output2 : ℕ
example-output2 = 71503

-- Parse

valid-number : Exp
valid-number = (((singleton ' ') ⋆) ∙ (singleton ' ')) ∙ Exp-ℕ

valid-content : Exp
valid-content = (Exp-from-String' "Time:") ∙ (valid-number ⋆)
              ∙ (Exp-from-String' "\nDistance:") ∙ (valid-number ⋆)

parse-number : ∀ {s} → (s ∈ valid-number) → ℕ
parse-number (prod _ _ n) = parse-ℕ n

parse-content : ∀ {s} → (s ∈ valid-content) → List ℕ × List ℕ
parse-content (prod _ _ (prod _ ts (prod _ _ ds))) = parse-numbers ts , parse-numbers ds
  where
    parse-numbers : ∀ {s} → (s ∈ (valid-number ⋆)) → List ℕ
    parse-numbers = Exp-star-map parse-number

parse-input : String → Maybe Parsed
parse-input = Maybe.map (Product.uncurry List.zip) ∘ generic-parser valid-content parse-content

_ : parse-input example-input ≡ just example-parsed
_ = refl

-- Solvers

open import Data.Float as ℝ using () renaming (Float to ℝ)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ℤₚ
open import Relation.Nullary using (Dec)
-- import Agda.Builtin.Unit as Unit

ℝ-is-ℤ : ℝ → Bool
ℝ-is-ℤ f = Maybe-ℤ-equal ℝ.⌊ f ⌋ ℝ.⌈ f ⌉
  where
    Maybe-ℤ-equal : Maybe ℤ → Maybe ℤ → Bool
    Maybe-ℤ-equal nothing _ = false
    Maybe-ℤ-equal _ nothing = false
    Maybe-ℤ-equal (just f) (just g) = Dec.does (f ℤ.≟ g)

discriminant : ℤ → ℤ → ℤ → ℤ
discriminant a b c = (b ℤ.* b) ℤ.- ((ℤ.+ 4) ℤ.* a ℤ.* c)

-- solve-quadratic-eq : (a : ℤ) → (b : ℤ) → (c : ℤ) → ((ℤ.+ 0) ℤ.≤ discriminant a b c) → ℝ × ℝ
-- solve-quadratic-eq a b c _ = Utils.diagonal-map (λ x → x ℝ.÷ (ℝ.fromℕ 2)) (l ℝ.- r) (l ℝ.+ r)
solve-quadratic-eq : (a : ℤ) → (b : ℤ) → (c : ℤ) → ℝ × ℝ
solve-quadratic-eq a b c = Utils.diagonal-map (λ x → x ℝ.÷ (ℝ.fromℕ 2)) (l ℝ.- r) (l ℝ.+ r)
  where
    l : ℝ
    l = ℝ.- (ℝ.fromℤ b)
    
    r : ℝ
    r = ℝ.sqrt $ ℝ.fromℤ $ discriminant a b c

cc : (a : ℤ) → (b : ℤ) → (c : ℤ) → Maybe ℕ
cc a b c = Maybe.map count $ hola $ solve-quadratic-eq a b c
  where
    offset : ℤ
    offset = if ℝ-is-ℤ (ℝ.sqrt $ ℝ.fromℤ $ discriminant a b c) then (ℤ.+ 0) else (ℤ.+ 1)
    
    count : ℤ × ℤ → ℕ
    count (l , r) = ℤ.∣ (r ℤ.- l ℤ.- (ℤ.+ 1) ℤ.+ offset) ∣

    hola : ℝ × ℝ → Maybe (ℤ × ℤ)
    hola = Product.uncurry Maybe.zip ∘ Product.uncurry (Utils.diagonal-map ℝ.⌊_⌋)

aaa : ℕ × ℕ → Maybe ℕ
-- aaa (t , d) = if Δ-is-positive then (cc a b c {! Bool.T? ?  !}) else just 0
aaa (t , d) = if Δ-is-positive then (cc a b c) else just 0
  where
    a = (ℤ.- (ℤ.+ 1))
    b = (ℤ.+ t)
    c = (ℤ.- (ℤ.+ d))

    Δ-is-positive : Bool
    Δ-is-positive = (ℤ.+ 0) ℤ.≤ᵇ discriminant a b c

solve1 : String → Maybe ℕ
solve1 = Maybe.map (solve)  ∘ parse-input
  where
    aa : ℕ × ℕ → ℕ
    aa (t , d) = List.length $ List.filter (λ d' → d <? d') $ List.map (λ i → i * (t ∸ i)) $ List.upTo t

    -- solve : Parsed → List (Maybe ℕ)
    solve : Parsed → ℕ
    solve = List.product ∘ List.map aa

solve2 : String → Maybe ℕ
solve2 = Utils.Maybe-idempotent ∘ Maybe.map (solve)  ∘ parse-input
  where
    bb : List (ℕ × ℕ) → ℕ × ℕ
    bb = Product.uncurry (Utils.diagonal-map (xx 0 ∘ List.reverse)) ∘ List.unzip
      where
        xx : ℕ → List ℕ → ℕ
        xx m [] = 0
        xx m (n ∷ ns) = (10 ^ m) * n + (xx (m + (List.length (toDecimalChars n))) ns)

    solve : Parsed → Maybe ℕ
    solve = aaa ∘ bb

_ : solve1 example-input ≡ just example-output1
_ = refl

_ : solve2 example-input ≡ just example-output2
_ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 ℕ-show "day06" "Day 06"
 