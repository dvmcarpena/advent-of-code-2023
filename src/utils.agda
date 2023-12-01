{-# OPTIONS --without-K --guardedness #-}

module utils where

-- Imports

open import Level using (Level)
open import Function.Base using (_∘_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Data.Bool.Base using (Bool)
open import Data.Product using (_×_)
open import Data.List.Base using (List; _∷_; [])
open import Data.Vec.Base using (Vec; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)

-- Variables

-- TODO

-- Data

EnrichedRunner : Set
EnrichedRunner = (String → String) × String × String × Bool

-- Utils

-- TODO
