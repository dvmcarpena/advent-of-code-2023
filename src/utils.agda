{-# OPTIONS --cubical-compatible --safe #-}

module utils where

-- Imports

open import Level using (Level)
open import Function.Base using (_∘_; id)
open import Relation.Binary using (DecPoset)
open import Data.Nat.Base using (ℕ)
open import Data.Char.Properties as Charₚ using ()
open import Data.String.Base as String using (String; _++_)
open import Data.Bool.Base using (Bool)
open import Data.Product using (_×_; _,_; <_,_>)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_)
open import Data.Vec.Base using (Vec; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Text.Regex.Base (DecPoset.preorder Charₚ.≤-decPoset) as Regex using (Exp)

-- Variables

private
  variable
    ℓ₁ : Level
    A : Set ℓ₁

-- Runner

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

-- Utils

duplicate : A → A × A
duplicate a = (a , a)

List-propagate-maybe : List (Maybe A) → Maybe (List A)
List-propagate-maybe [] = just []
List-propagate-maybe (nothing ∷ xs) = nothing
List-propagate-maybe ((just x) ∷ xs) with (List-propagate-maybe xs)
... | nothing = nothing
... | (just v) = just (x ∷ v)
    
List⁺-propagate-maybe : List⁺ (Maybe A) → Maybe (List⁺ A)
List⁺-propagate-maybe (nothing List⁺.∷ xs) = nothing
List⁺-propagate-maybe (just x List⁺.∷ xs) with (List-propagate-maybe xs)
... | nothing = nothing
... | (just v) = just (x List⁺.∷ v)

Maybe-idempotent : Maybe (Maybe A) → Maybe A
Maybe-idempotent nothing = nothing
Maybe-idempotent (just nothing) = nothing
Maybe-idempotent (just (just a)) = just a

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
