module Common.solver where

open import Common.types
open import Term.solver
open import Data.List 
  using (List; _∷_; length)
open import Data.Nat 
  using (ℕ; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Data.Bool
open import Data.Maybe
  using (Maybe)

-- Generic solve function. Example for different domain (real) added
solve : {c : 𝒞} (right : List (ℒ c)) → ((length right ≡ᵇ 0) ≡ false) → Subst c → Maybe (Subst c)
solve {term} (first ∷ right) refl _ = unify (first ∷ right)
-- solve {real} (first ∷ right) refl _ = simplex