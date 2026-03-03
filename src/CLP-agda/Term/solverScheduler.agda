{-# OPTIONS --allow-unsolved-metas #-}

module Term.solverScheduler where

open import Term.types
open import Term.utilities
open import Term.ftUtilsDerivation

open import Data.Bool hiding (_≟_)
open import Data.List
open import Data.List.Base
open import Data.List.Membership.DecSetoid using (_∈?_)
open import Data.Sum
open import Data.Product
open import Function.Base
open import Data.Maybe hiding (_>>=_)

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

decToBool : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

{-# TERMINATING #-}
nubBy : {A : Set} → (A → A → Bool) → List A → List A
nubBy _ []       = []
nubBy pred (x ∷ xs) = x ∷ nubBy pred (filterᵇ (λ y → not (pred x y)) xs)

headMaybe : {A : Set} → List A → Maybe A
headMaybe []       = nothing
headMaybe (x ∷ xs) = just x

equal : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄ 
  → Σᵢ 𝒞 (λ _ → ⊤) Code Constraint → Σᵢ 𝒞 (λ _ → ⊤) Code Constraint → Bool
equal (_:-:_ c₀ _) (_:-:_ c₁ _) with c₀ ≟ c₁
... | yes refl = true
... | no _ = false

{-# TERMINATING #-}
defaultSchedule₀ : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → List (Σᵢ 𝒞 (λ _ → ⊤) Code Constraint)
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
  → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
defaultSchedule₀ ⦃ dec ⦄ ((_:-:_ c _ ⦃ instCode ⦄ ⦃ instCns ⦄) ∷ xs) unifications = 
  let res = (solve c ⦃ dec ⦄ ⦃ instCode ⦄ ⦃ instCns ⦄ ∘ catMaybes ∘ Data.List.map (getPermission c)) unifications in
    (headMaybe ∘ catMaybes ∘ Data.List.map (λ y → defaultSchedule₀
      ((nubBy equal ∘ _++_ xs ∘ 
      Data.List.map (λ {(inj₁ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCns ⦄ ⦃ instCode1 ⦄ ⦃ instCns1 ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCns ⦄ ⦃ instCode1 ⦄ ⦃ instCns1 ⦄ ;
                        (inj₂ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCns ⦄ ⦃ instCode1 ⦄ ⦃ instCns1 ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCns ⦄ ⦃ instCode1 ⦄ ⦃ instCns1 ⦄}) ∘ 
      catMaybes ∘ 
      (Data.List.map ∘ getElse) c) 
      y) y)) res
defaultSchedule₀ [] unifications = just unifications

defaultSchedule : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
  → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
defaultSchedule unifications = defaultSchedule₀ (
  (nubBy equal ∘ 
   Data.List.map (λ {(inj₁ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCns ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCns ⦄ ;
                     (inj₂ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCns ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCns ⦄})) unifications) unifications