open import Term.types

open import Data.List
open import Data.Sum
open import Data.Product
open import Function.Base
open import Data.Maybe hiding (_>>=_)

module Term.solverScheduler where

schedule : 
  {Index : Set} 
  {Code : (Index → Set)} 
  {Constraint : Set} 
  {i : Index}
  → ⦃ Solver Index Code Constraint ⦄
  → List ((Σ Index (ℒ ∘ Code)) ⊎ Constraint)
  → (Maybe ∘ List) (List ((Σ Index (ℒ ∘ Code)) ⊎ Constraint))
schedule ((inj₁ (witness , x)) ∷ xs) = solve witness ((inj₁ (witness , x)) ∷ xs)