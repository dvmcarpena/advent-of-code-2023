{-# OPTIONS --cubical-compatible --safe #-}

module utils where

-- Imports

open import Level using (Level)
open import Function.Base using (_∘_; id; _$_)
open import Relation.Binary using (DecPoset)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (ℕ; _+_; _*_; _∸_)
open import Data.Char.Base as Char using (Char)
open import Data.Char.Properties as Charₚ using ()
open import Data.String as String using (String; _++_)
open import Data.Bool.Base using (Bool; true)
open import Data.Product using (_×_; _,_; <_,_>)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as Maybe
open import Data.List.Base as List using (List; _∷_; [])
import Data.List.Categorical as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_)
import Data.List.NonEmpty.Categorical as List⁺
open import Data.Vec.Base using (Vec; _∷_; [])
import Text.Regex.Base (DecPoset.preorder Charₚ.≤-decPoset) as Regex
open import Text.Regex Charₚ.≤-decPoset

-- Variables

private
  variable
    ℓ₁ ℓ₂ : Level
    A : Set ℓ₁
    B : Set ℓ₂

-- Runner

module Runner where

  Runner : Set
  Runner = (String → String) × String × String

  mkRunner : (String → Maybe A) 
          → (String → Maybe A) 
          → (A → String) 
          → String 
          → String 
          → Runner
  mkRunner {ℓ₁} {A} solve1 solve2 A-show file display = (format-results ∘ < solve1 , solve2 > , file , display)
    where
      format-result : (Maybe A) → String
      format-result nothing = "Invalid input format!"
      format-result (just a) = A-show a
      
      format-results : (Maybe A) × (Maybe A) → String
      format-results (a₁ , a₂) = "Part One: " ++ format-result a₁ ++ "\nPart Two: " ++ format-result a₂

open Runner public

-- Utils

module Utils where

  duplicate : A → A × A
  duplicate a = (a , a)

  enumerate : List A → List (ℕ × A)
  enumerate as = rec-enumerate 0 as 
    where
      rec-enumerate : ℕ → List A → List (ℕ × A)
      rec-enumerate _ [] = []
      rec-enumerate n (a ∷ as) = (n , a) ∷ (rec-enumerate (n + 1) as)
    
  Prod-List-concat : List ((List A) × (List B)) → (List A) × (List B)
  Prod-List-concat [] = [] , []
  Prod-List-concat ((a , b) ∷ ps) = (λ (as , bs) → (a List.++ as) , (b List.++ bs)) $ Prod-List-concat ps

  List-propagate-maybe : List (Maybe A) → Maybe (List A)
  List-propagate-maybe = List.TraversableA.mapA Maybe.applicative id
  -- List-propagate-maybe [] = just []
  -- List-propagate-maybe (nothing ∷ xs) = nothing
  -- List-propagate-maybe ((just x) ∷ xs) with (List-propagate-maybe xs)
  -- ... | nothing = nothing
  -- ... | (just v) = just (x ∷ v)
      
  List⁺-propagate-maybe : List⁺ (Maybe A) → Maybe (List⁺ A)
  List⁺-propagate-maybe = List⁺.TraversableA.mapA Maybe.applicative id
  -- List⁺-propagate-maybe (nothing List⁺.∷ xs) = nothing
  -- List⁺-propagate-maybe (just x List⁺.∷ xs) with (List-propagate-maybe xs)
  -- ... | nothing = nothing
  -- ... | (just v) = just (x List⁺.∷ v)

  Maybe-idempotent : Maybe (Maybe A) → Maybe A
  Maybe-idempotent nothing = nothing
  Maybe-idempotent (just nothing) = nothing
  Maybe-idempotent (just (just a)) = just a

module Expression where

  Exp-ℕ : Exp
  Exp-ℕ = [ '1' ─ '9' ∷ [] ] ∙ [ '0' ─ '9' ∷ [] ] ⋆

  Exp-reverse : Exp → Exp
  Exp-reverse (e1 Regex.∙ e2) = (Exp-reverse e2) Regex.∙ (Exp-reverse e1)
  Exp-reverse (e1 Regex.∣ e2) = (Exp-reverse e1) Regex.∣ (Exp-reverse e2)
  Exp-reverse (e Regex.⋆) = (Exp-reverse e) Regex.⋆
  Exp-reverse = id

  Exp-concatenate : List⁺ Exp → Exp
  Exp-concatenate (e1 List⁺.∷ es) with es
  ... | []         = e1
  ... | (e2 ∷ ess) = e1 Regex.∙ (Exp-concatenate (e2 List⁺.∷ ess))

  Exp-from-String : String → Maybe Exp
  Exp-from-String = Maybe.map Exp-concatenate ∘ List⁺.fromList ∘ List.map Regex.singleton ∘ String.toList

  Exp-from-String' : (s : String) → Maybe.From-just (Exp-from-String s)
  Exp-from-String' = Maybe.from-just ∘ Exp-from-String

  Exp-from-Strings : List String → Maybe Exp
  Exp-from-Strings [] = nothing
  Exp-from-Strings (s1 ∷ ss) with ss
  ... | []         = (Exp-from-String s1)
  ... | (s2 ∷ sss) with (Exp-from-String s1) | (Exp-from-Strings (s2 ∷ sss))
  ...       | nothing | _       = nothing
  ...       | just _  | nothing = nothing
  ...       | just a  | just b  = just (a Regex.∣ b)

  Exp-from-Strings' : (ss : List String) → Maybe.From-just (Exp-from-Strings ss)
  Exp-from-Strings' = Maybe.from-just ∘ Exp-from-Strings

module Parser where

  open Expression using (Exp-ℕ)

  parse-ℕ : ∀ {s} → (s ∈ Exp-ℕ) → ℕ
  parse-ℕ {s} _ = convert $ List.map (λ c → (Char.toℕ c) ∸ (Char.toℕ '0')) s
    where
      convert : List ℕ → ℕ
      convert = List.foldl (λ acc d → 10 * acc + d) 0
  
  generic-parser-by-lines : (e : Exp) 
    → (∀ {s} → (s ∈ e) → A) 
    → String
    → Maybe (List⁺ A)
  generic-parser-by-lines {ℓ₁} {A} e to-A = Utils.Maybe-idempotent ∘ Maybe.map generic-parse-lines ∘ List⁺.fromList ∘ String.lines
    where
      regex : Regex
      regex = record
        { fromStart  = true
        ; tillEnd    = true
        ; expression = e
        }

      generic-parse-line : List Char → Maybe A
      generic-parse-line s = Maybe.map (to-A ∘ Match.match) $ Maybe.decToMaybe $ search s regex

      generic-parse-lines : List⁺ String → Maybe (List⁺ A)
      generic-parse-lines = Utils.List⁺-propagate-maybe ∘ List⁺.map (generic-parse-line ∘ String.toList)
