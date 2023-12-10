{-# OPTIONS --with-K --safe #-}

module utils-with-k where

-- Imports

open import Level using (Level)
open import Function.Base using (_∘_; id; _$_)
open import Relation.Binary using (DecPoset)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (ℕ; _+_; _*_; _∸_)
open import Data.Char.Base as Char using (Char)
open import Data.Char.Properties as Charₚ using ()
open import Data.String as String using (String; _++_)
open import Data.Bool.Base using (Bool)
open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂)
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

-- Utils

parse-6-cases : ∀ {s e1 e2 e3 e4 e5 e6} 
            → ((x : (s ∈ e1) ⊎ (s ∈ e2) ⊎ (s ∈ e3) ⊎ (s ∈ e4) ⊎ (s ∈ e5) ⊎ (s ∈ e6)) → A)
            → (s ∈ (e1 Regex.∣ e2 Regex.∣ e3 Regex.∣ e4 Regex.∣ e5 Regex.∣ e6))
            → A
parse-6-cases f (sum (inj₁ x)) = f (inj₁ x)
parse-6-cases f (sum (inj₂ (sum (inj₁ x)))) = f (inj₂ (inj₁ x))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₁ x)))))) = f (inj₂ (inj₂ (inj₁ x)))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₁ x)))))))) = f (inj₂ (inj₂ (inj₂ (inj₁ x))))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₁ x)))))))))) = f (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))
parse-6-cases f (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₂ (sum (inj₂ x)))))))))) = f (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))

Exp-star-map : ∀ {s e} → (∀ {t} → (t ∈ e) → A) → (s ∈ (e Regex.⋆)) → List (A)
Exp-star-map f (star (sum (inj₁ _))) = []
Exp-star-map f (star (sum (inj₂ (prod _ p1 r)))) = (f p1) ∷ (Exp-star-map f r)

Exp-star-fold : ∀ {s e} → (∀ {t} → B → (t ∈ e) → B × A) → B → (s ∈ (e Regex.⋆)) → List (A)
Exp-star-fold f b (star (sum (inj₁ _))) = []
Exp-star-fold f b (star (sum (inj₂ (prod _ p1 r)))) = (proj₂ f1) ∷ (Exp-star-fold f (proj₁ f1) r)
  where
    f1 = f b p1
