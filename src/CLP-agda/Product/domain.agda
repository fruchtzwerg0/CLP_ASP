module Product.domain where

open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.List
open import Function.Base

open import Generics
open import Term.ftUtilsDerivation
open import Term.types

data ×Logic (A : Set) : Set where
  _∶_ : A → A → ×Logic A
  var× : ℕ → ×Logic A

×D : HasDesc ×Logic
×D = deriveDesc ×Logic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  makeVar× : ∀ {A} → MakeVar (×Logic A)
          makeVar× .fresh = var×
          makeVar× .new = var× 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  unifyDisunify× : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (×Logic A)
          unifyDisunify× = deriveFTUtils ×D

fold× = deriveFold ×D

apply× : ∀ {A} → (apply : ℕ → A → A → A) → ℕ → ×Logic A → ×Logic A → ×Logic A
apply× app x subst = fold× (λ a b → app a ∶ app b) (λ y → if x ≡ᵇ y then subst else (var× y))

zipMatch× : ∀ {A} → ×Logic A → ×Logic A → (Maybe ∘ List ∘ ℒ) A
zipMatch× (a ∶ b) (x ∶ y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatch× _ _ = nothing

incrementFD : ∀ {A} → ℕ → ×Logic A → ×Logic A
incrementFD x = fold× _∶_ (λ y → var× (x + y))