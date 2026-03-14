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

cForall₀ : 
  ∀ {𝒞 Code Constraint}
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ℕ
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → Bool
cForall₀ _ [] _ = false
cForall₀ {C}{Code}{Constraint} v (newConstraints ∷ xs) store with partitionᵇ (any (_≡ᵇ_ v) ∘ collectVarsᵥ C Code Constraint) newConstraints
... | (x , y) with y ++ store
... | newStore = false
  --(any ∘ cForall₀ v xs ∘ Data.List.map (_++_ newStore) ∘ filterᵇ (Data.Bool.not ∘ null) 
  --∘ Data.List.map (schedule ∘ [_] ∘ _++_ newStore ∘ [_] ∘ negateConstraint)) x

cForall : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ℕ
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
cForall ⦃ sched ⦄ v constraints with cForall₀ ⦃ sched ⦄ v constraints []
... | true = constraints
... | false = []