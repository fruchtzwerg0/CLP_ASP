{-# OPTIONS --allow-unsolved-metas #-}

module ASP.asp where

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
open import ASP.nmr
open import ASP.loops

aspExecute : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → Clause ConcreteAtom validate 𝒞 Code Constraint
  → Body ConcreteAtom (validate bodyOfRule) 𝒞 Code Constraint
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
aspExecute program goal = 
  clpExecute (computeNMR program ∘ computeDual program) addNMR 