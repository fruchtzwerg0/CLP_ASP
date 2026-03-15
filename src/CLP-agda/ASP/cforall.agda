{-# OPTIONS --allow-unsolved-metas #-}

module ASP.cforall where

open import Term.types hiding (_>>=_)
open import Term.ftUtilsDerivation
open import Term.utilities
open import ASP.types
open import Views.find
open import Views.findall
open import Data.Bool hiding (_≟_)
open import Data.String 
  using (String; _==_)
open import Data.Nat hiding (equal; _≟_)
open import Data.List
open import Data.List.Base
open import Data.List.Membership.DecSetoid using (_∈?_)
open import Data.Maybe 
  using (Maybe; just; nothing; map; is-just)
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Function.Base

open import Generics

open import Term.clp
open import ASP.dual

addToConstraintStore : 
  ∀ {Atom 𝒞 Code Constraint}
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
addToConstraintStore store c = Data.List.map (_∷_ c) store

cForall₀ : 
  ∀ {Atom 𝒞 Code Constraint}
  → {Custom : Set}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ℕ
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → Bool
cForall₀ _ [] _ = false
cForall₀ {Atom}{C}{Code}{Constraint} v ((_ , answer) ∷ answers) store with 
  Data.List.map (partitionᵇ (any (_≡ᵇ_ v) ∘ collectVarsᵥ {_}{Atom} C Code Constraint)) answer
... | xy with (concat ∘ Data.List.map (λ z → (Data.List.map (_++_ z ∘ proj₂)) xy)) store
... | newStore with
  (filterᵇ (Data.Bool.not ∘ null) 
  ∘ concat ∘ Data.List.map (concat ∘ Data.List.map (schedule ∘ addToConstraintStore newStore ∘ negateConstraint))) (Data.List.map proj₁ xy)
... | [] = true
... | xs = cForall₀ v answers xs

cForall : 
  ∀ {Atom 𝒞 Code Constraint}
  → {Custom : Set}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ℕ
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
  → Bool
cForall ⦃ sched ⦄ v answers = cForall₀ ⦃ sched ⦄ v answers []