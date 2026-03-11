module ASP.types where

open import Data.Bool hiding (not ; _∧_)
open import Data.Char
open import Data.String hiding (head; _++_)
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.List hiding (head)
open import Data.Product
open import Data.Sum

open import Term.types

open import Function.Base


data ASPAtom (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  wrap : Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → ASPAtom Atom 𝒞 Code Constraint
  forAll : Σᵢ 𝒞 Code Code Constraint → ASPAtom Atom 𝒞 Code Constraint → ASPAtom Atom 𝒞 Code Constraint
  nmrCheck : ASPAtom Atom 𝒞 Code Constraint
  chk : ℕ → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → ASPAtom Atom 𝒞 Code Constraint

record ASPUtils (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    isNot : Atom → Bool
    isFalse : Atom → Bool
    not : Atom → Atom
    toggle : Atom → Atom
    fillWithVars : Atom → ℕ → Atom

open ASPUtils ⦃...⦄ public