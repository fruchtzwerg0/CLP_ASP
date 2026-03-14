{-# OPTIONS --allow-unsolved-metas #-}

module ASP.loops where

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

open import ASP.dual
open import ASP.cforall

checkCHS :
  ∀ {Atom 𝒞 Code Constraint}
  → (List ∘ List) ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)
  → List Atom
  → Atom
  → (List ∘ List) ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c) ⊎ ⊤
checkCHS (constraint ∷ constraints) x y = 
  if any (unifyDisunify ∘ _++_ (y ∷ constraint)) x
  then inj₂ (record {})
  else (inj₁ ∘ Data.List.map ([_] ∘ _≠ℒ_ y) ∘ Data.List.map (unifyDisunify ∘ _++_ (toggle y ∷ constraints))) x

checkLoops :
  ∀ {Atom 𝒞 Code Constraint}
  → (List ∘ List) ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)
  → List Atom
  → Atom
  → ℕ
  → (List ∘ List) ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c) ⊎ ⊤
checkLoops _ [] y n = inj₂ (record {})
checkLoops (constraint ∷ constraints) (x ∷ xs) y n = 
  if unifyDisunify x y
  then
    if n ≡ᵇ 0 
    then inj₁ []
    else 
      if n mod 2 ≡ᵇ 0
      then inj₁ (unifyDisunify x y)
      else checkLoops xs y (if isNot x then suc n else n)
  else checkLoops xs y (if isNot x then suc n else n)

checkASP : 
  ∀ {Atom 𝒞 Code Constraint}
  → (List ∘ List) ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)
  → List Atom
  → List Atom
  → Atom
  → List Atom × (List ∘ List) ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)
checkASP constraints chs xs y with checkCHS constraints chs y
... | inj₂ _ = constraints                                    -- CHS success
... | inj₁ newConstraints with checkLoops newConstraints xs y -- CHS neutral
... | inj₂ _ = eval y chs xs newConstraints                   -- Loop neutral
... | inj₁ [] = []                                            -- Loop fail
... | inj₁ (x ∷ xs) = (x ∷ xs)                                -- Loop success

interceptASP :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List Atom × List Atom
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (Literal Atom 𝒞 Code Constraint)
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List (List Atom × List Atom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
interceptASP (chs , stack) program (constraint cn ∷ goals) constraints = 
  eval (chs , stack) program (constraint cn ∷ goals) constraints
interceptASP (chs , stack) program (atom at ∷ goals) constraints with (λ { (forAll v _) → just v ; _ → nothing }) at
interceptASP (chs , stack) program (atom at ∷ goals) constraints | nothing = 
  checkASP constraints chs stack at
interceptASP (chs , stack) program (atom at ∷ goals) constraints | just v with varName v
interceptASP (chs , stack) program (atom at ∷ goals) constraints | just v | just n =
  eval (chs , stack) program (atom at ∷ goals) (cForall n constraints)
interceptASP (chs , stack) program (atom at ∷ goals) constraints | just v | nothing =
  checkASP constraints chs stack at