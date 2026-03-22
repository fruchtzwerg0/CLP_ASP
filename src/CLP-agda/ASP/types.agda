module ASP.types where

open import Data.Bool hiding (not ; _∧_)
open import Data.Char
open import Data.String hiding (head; _++_)
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.List hiding (head)
open import Data.Product
open import Data.Sum

open import CLP.types

open import Function.Base

-- AST used for ASP. Wraps atoms and gives them additional information that can be retrieved by the ASP parameterization.

data ASPAtom (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  wrap : Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → ASPAtom Atom 𝒞 Code Constraint
  forAll : Σᵢ 𝒞 Code Code Constraint → ASPAtom Atom 𝒞 Code Constraint → ASPAtom Atom 𝒞 Code Constraint
  nmrCheck : ASPAtom Atom 𝒞 Code Constraint
  chk : ℕ → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → ASPAtom Atom 𝒞 Code Constraint

-- Utilities that users need to implement for their atom type when planning to use ASP.

record ASPUtils (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    isNot : Atom → Bool
    isFalse : Atom → Bool
    not : Atom → Atom
    toggle : Atom → Atom
open ASPUtils ⦃...⦄ public