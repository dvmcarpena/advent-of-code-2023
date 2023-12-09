{-# OPTIONS --with-K --safe #-}

module day01 where

-- Imports

open import Function.Base using (_$_; _∘_; id)
open import Data.Product using (_×_; _,_; <_,_>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
open import Data.Bool.Base using (if_then_else_; true; false; _∧_)
open import Data.Nat.Show renaming (readMaybe to ℕ-readMaybe; show to ℕ-show)
open import Data.List.Relation.Unary.All
open import Data.Product as Product using (∃-syntax; _,′_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel; Decidable)
open import Relation.Nullary.Decidable using (True; False; from-yes)
import Data.Char.Properties as Charₚ
open import Relation.Binary using (DecPoset)
open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Text.Regex.Base (DecPoset.preorder Charₚ.≤-decPoset) as Regex using ()
open import Text.Regex Charₚ.≤-decPoset renaming (sum to ∈-sum)

open import utils using (Runner; mkRunner; List⁺-propagate-maybe; Maybe-idempotent; duplicate; Exp-reverse; Exp-from-Strings')

-- Data

Output : Set
Output = ℕ

Output-show : Output → String
Output-show = ℕ-show

example-input1 : String
example-input1 = "1abc2\npqr3stu8vwx\na1b2c3d4e5f\ntreb7uchet"

example-parsed1 : List⁺ (ℕ × ℕ)
example-parsed1 = (1 ,′ 2) ∷⁺ (3 ,′ 8) ∷⁺ (1 ,′ 5) ∷⁺ List⁺.[ (7 ,′ 7) ]

example-output1 : ℕ
example-output1 = 142

example-input2 : String
example-input2 = "two1nine\neightwothree\nabcone2threexyz\nxtwone3four\n4nineeightseven2\nzoneight234\n7pqrstsixteen"

example-parsed2 : List⁺ (ℕ × ℕ)
example-parsed2 = (2 ,′ 9) ∷⁺ (8 ,′ 3) ∷⁺ (1 ,′ 3) ∷⁺ (2 ,′ 4) ∷⁺ (4 ,′ 2) ∷⁺ (1 ,′ 4) ∷⁺ List⁺.[ (7 ,′ 6) ]

example-output2 : ℕ
example-output2 = 281

-- Parse

digits : Exp
digits = Exp-from-Strings' ("1" ∷ "2" ∷ "3" ∷ "4" ∷ "5" ∷ "6" ∷ "7" ∷ "8" ∷ "9" ∷ [])

_ : True ((String.toList "1") ∈? digits)
_ = _

_ : False ((String.toList "a") ∈? digits)
_ = _

written-digits : Exp
written-digits = Exp-from-Strings' ("one" ∷ "two" ∷ "three" ∷ "four" ∷ "five" ∷ "six" ∷ "seven" ∷ "eight" ∷ "nine" ∷ [])

_ : True ((String.toList "one") ∈? written-digits)
_ = _

_ : False ((String.toList "a") ∈? written-digits)
_ = _

h : ∀ {e1 e2 e3 e4 e5 e6 e7 e8 e9} → (s : List Char) → (s ∈ (e1 Regex.∣ e2 Regex.∣ e3 Regex.∣ e4 Regex.∣ e5 Regex.∣ e6 Regex.∣ e7 Regex.∣ e8 Regex.∣ e9)) → ℕ
h _ (∈-sum (inj₁ _)) = 1
h _ (∈-sum (inj₂ (∈-sum (inj₁ _)))) = 2
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₁ _)))))) = 3
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₁ _)))))))) = 4
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₁ _)))))))))) = 5
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₁ _)))))))))))) = 6
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₁ _)))))))))))))) = 7
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₁ _)))))))))))))))) = 8
h _ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ (∈-sum (inj₂ _)))))))))))))))) = 9

map-exp-digits : (s : List Char) → (s ∈ digits) → ℕ
map-exp-digits = h

map-exp-all-digits : (s : List Char) → (s ∈ (digits Regex.∣ written-digits)) → ℕ
map-exp-all-digits s (Regex.sum (inj₁ p)) = map-exp-digits s p
map-exp-all-digits s (∈-sum (inj₂ p)) = h s p

map-exp-all-digits-reversed : (s : List Char) → (s ∈ (digits Regex.∣ Exp-reverse written-digits)) → ℕ
map-exp-all-digits-reversed s (∈-sum (inj₁ p)) = map-exp-digits s p
map-exp-all-digits-reversed s (∈-sum (inj₂ p)) = h s p

regex-digits : Regex
regex-digits = record
  { fromStart  = false
  ; tillEnd    = false
  ; expression = digits
  }

regex-all-digits : Regex
regex-all-digits = Regex.updateExp (λ e → e ∣ written-digits) regex-digits

regex-all-digits-reversed : Regex
regex-all-digits-reversed = Regex.updateExp (λ e → e ∣ Exp-reverse written-digits) regex-digits

generic-search : (r : Regex) 
  → ((s : List Char) → (s ∈ (Regex.expression r)) → ℕ) 
  → List Char 
  → Maybe ℕ
generic-search r to-ℕ s = Maybe.map match-to-ℕ $ Maybe.decToMaybe $ search s r
  where
    match-to-ℕ : Match (Span r _≡_) s (Regex.expression r) → ℕ
    match-to-ℕ m = to-ℕ (Match.list m) (Match.match m)

parse-input : (List Char → Maybe ℕ) → (List Char → Maybe ℕ) → String → Maybe (List⁺ (ℕ × ℕ))
parse-input search-first search-last = Maybe-idempotent ∘ Maybe.map parse-lines ∘ List⁺.fromList ∘ String.lines
  where
    search-first-and-last : List Char → Maybe (ℕ × ℕ)
    search-first-and-last s = Maybe.zip (search-first s) (search-last s)

    parse-lines : List⁺ String → Maybe (List⁺ (ℕ × ℕ))
    parse-lines = List⁺-propagate-maybe ∘ List⁺.map (search-first-and-last ∘ String.toList)

parse-input1 : String → Maybe (List⁺ (ℕ × ℕ))
parse-input1 = parse-input search-first (search-first ∘ List.reverse)
  where
    search-first : List Char → Maybe ℕ
    search-first = generic-search regex-digits map-exp-digits

parse-input2 : String → Maybe (List⁺ (ℕ × ℕ))
parse-input2 = parse-input search-first search-last
  where
    search-first : List Char → Maybe ℕ
    search-first = generic-search regex-all-digits map-exp-all-digits

    search-last : List Char → Maybe ℕ
    search-last = generic-search regex-all-digits-reversed map-exp-all-digits-reversed ∘ List.reverse

_ : < parse-input1 , parse-input2 > "1ad3sas2" ≡ duplicate (just (List⁺.[ (1 ,′ 2) ]))
_ = refl

_ : < parse-input1 , parse-input2 > "" ≡ duplicate nothing
_ = refl

_ : < parse-input1 , parse-input2 > "asdasdasd" ≡ duplicate nothing
_ = refl

_ : < parse-input1 , parse-input2 > "1ad3sas2\nasdasdasd" ≡ duplicate nothing
_ = refl

_ : parse-input1 example-input1 ≡ just example-parsed1
_ = refl

_ : parse-input2 "onead3sas2" ≡ just (List⁺.[ (1 ,′ 2) ])
_ = refl

_ : parse-input2 "onead3sasnine" ≡ just (List⁺.[ (1 ,′ 9) ])
_ = refl

_ : parse-input2 example-input2 ≡ just example-parsed2
_ = refl

-- Solvers

solve : List⁺ (ℕ × ℕ) → ℕ
solve = List.sum ∘ List⁺.toList ∘ List⁺.map convert
  where
    convert : ℕ × ℕ → ℕ
    convert (d1 , d0) = 10 * d1 + d0

solve1 : String → Maybe Output
solve1 = Maybe.map (solve) ∘ parse-input1

solve2 : String → Maybe Output
solve2 = Maybe.map (solve) ∘ parse-input2

_ : solve (List⁺.[ (1 ,′ 3) ]) ≡ 13
_ = refl

_ : solve ((5 ,′ 4) ∷⁺ List⁺.[ (1 ,′ 3) ]) ≡ 67
_ = refl

_ : solve example-parsed1 ≡ example-output1
_ = refl

_ : solve example-parsed2 ≡ example-output2
_ = refl

-- Runner

runner : Runner
runner = mkRunner solve1 solve2 Output-show "day01" "Day 01"
