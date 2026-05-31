module CLP.solverScheduler where

open import CLP.types
open import CLP.utilities
open import CLP.ftUtilsDerivation
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

-- Remove duplicates using a custom equality predicate
{-# TERMINATING #-}
nubBy : {A : Set} → (A → A → Bool) → List A → List A
nubBy _ []       = []
nubBy pred (x ∷ xs) = x ∷ nubBy pred (filterᵇ (λ y → not (pred x y)) xs)

-- Solver-tag equality: two Σᵢ are equal iff their 𝒞 tags match
equal : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄ 
  → Σᵢ 𝒞 (λ _ → ⊤) Code Constraint → Σᵢ 𝒞 (λ _ → ⊤) Code Constraint → Bool
equal (_:-:_ c₀ _) (_:-:_ c₁ _) with c₀ ≟ c₁
... | yes refl = true
... | no _ = false

-- Multi-solver scheduler (recursive step).
--
-- solver queue (xs): solvers still to be dispatched this round.
-- new:              cross-solver constraints introduced this round.
-- unifications:     accumulated bindings from all solvers so far.
--
-- For the head solver c:
--   1. Calls `solve c` with c's share of unifications and new,
--      passing cross-solver residuals as the carry-through payload.
--   2. For each branch (y , other) returned:
--      a. Adds any new solver tags seen in y's cross-solver output to xs.
--      b. Updates new = (cross-solver part of new) ++ (cross-solver part of y).
--      c. Updates unifications = c's new bindings ++ other.
--      d. Recurses.
-- Base case: empty queue → return current unifications as one branch.
{-# TERMINATING #-}
defaultSchedule₀ : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → List (Σᵢ 𝒞 (λ _ → ⊤) Code Constraint)           -- solver queue
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)  -- new constraints
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)  -- accumulated unifications
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
defaultSchedule₀ {C}{Code}{Constraint} ⦃ dec ⦄ ⦃ val ⦄ ⦃ cns ⦄ ((_:-:_ c _ ⦃ instCode ⦄ ⦃ instCns ⦄) ∷ xs) new unifications = 
  let res = solve 
              c 
              ⦃ dec ⦄ ⦃ instCode ⦄ ⦃ val ⦄ ⦃ instCns ⦄ ⦃ cns ⦄ 
              (occursᵥ {listOf mixedConstraint} {⊤} C Code Constraint) 
              (λ n sub → Data.List.map (applyMixedConstraint c n sub)) 
              ((catMaybes ∘ Data.List.map (getPermission c)) unifications)
              ((catMaybes ∘ Data.List.map (getPermission c)) new)
              ((catMaybes ∘ Data.List.map (getElse c)) unifications)
  in
    (concat ∘ Data.List.map (λ (y , other) → defaultSchedule₀
      ((nubBy equal ∘ _++_ xs ∘ 
      Data.List.map (λ {(inj₁ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCode1 ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCode1 ⦄ ;
                        (inj₂ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCode1 ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCode1 ⦄})) 
                    ((catMaybes ∘ Data.List.map (getElse c)) y)) 
      ((catMaybes ∘ Data.List.map (getElse c)) new ++ (catMaybes ∘ Data.List.map (getElse c)) y) 
      ((filterᵇ (is-just ∘ getPermission c)) y ++ other))) res
-- Empty queue: all solvers quiescent, return current unifications
defaultSchedule₀ [] _ unifications = unifications ∷ []

-- Entrypoint: build the initial solver queue from the tags present in new,
-- then call defaultSchedule₀ for each existing unification branch
defaultSchedule : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
-- Initial queue: one tag per distinct solver in new (payload erased to ⊤)
defaultSchedule new = concat ∘ Data.List.map (λ unification → defaultSchedule₀ (
  (nubBy equal ∘ 
   Data.List.map (λ {(inj₁ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCns ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCns ⦄ ;
                     (inj₂ (_:-:_ c x ⦃ instCode ⦄ ⦃ instCns ⦄)) → _:-:_ c (record {}) ⦃ instCode ⦄ ⦃ instCns ⦄})) new) new unification)