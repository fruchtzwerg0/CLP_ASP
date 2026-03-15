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

open import Term.clp

open import ASP.dual
open import ASP.cforall

{-# TERMINATING #-}
mod : ℕ → ℕ → ℕ
mod n zero = n
mod n m with compare n m
... | less _ _ = n
... | _ = mod (n ∸ m) m

checkCHS :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List Atom
  → Atom
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) ⊎ ⊤
checkCHS ⦃ dec ⦄ ⦃ at ⦄ constraints x y with 
  (any (Data.Bool.not ∘ null) ∘ Data.List.map (schedule ∘ concat ∘ Data.List.map (addToConstraintStore constraints) ∘ Data.List.map inj₁) ∘ catMaybes ∘ Data.List.map (zipMatch at y)) x
... | true = inj₂ (record {})
... | false = 
  (inj₁ ∘ {!   !} ∘ 
  filterᵇ (null ∘ schedule ∘ concat ∘ Data.List.map (addToConstraintStore constraints) ∘ Data.List.map inj₁) ∘ catMaybes ∘ Data.List.map (zipMatch at (toggle y))) x
-- Data.List.map (Data.List.map negateConstraint)
checkLoops :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List Atom
  → Atom
  → ℕ
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) ⊎ ⊤
checkLoops _ [] y n = inj₂ (record {})
checkLoops ⦃ dec ⦄ ⦃ at ⦄ constraints (x ∷ xs) y n with 
  zipMatch at x y Data.Maybe.>>= (just ∘ schedule ∘ concat ∘ Data.List.map (addToConstraintStore constraints) ∘ Data.List.map inj₁)
... | just result =
  if n ≡ᵇ 0 
  then inj₁ []
  else 
    if mod n 2 ≡ᵇ 0
    then inj₁ result
    else checkLoops constraints xs y (if isNot x then suc n else n)
... | nothing =
  checkLoops constraints xs y (if isNot x then suc n else n)

{-# TERMINATING #-}
checkASP : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → (ASPAtom Atom 𝒞 Code Constraint)
  → EvalType (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint (List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint))

{-# TERMINATING #-}
interceptASP :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → EvalType (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint (List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint))

checkASP at (chs , stack) program goals constraints with checkCHS constraints chs at
... | inj₂ _ = ((chs , stack) , constraints) ∷ []                                       -- CHS success
... | inj₁ newConstraints with checkLoops newConstraints stack at 0                     -- CHS neutral
... | inj₂ _ = eval interceptASP (chs , stack) program (atom at ∷ goals) newConstraints -- Loop neutral
... | inj₁ [] = []                                                                      -- Loop fail
... | inj₁ (x ∷ xs) = ((chs , stack) , x ∷ xs) ∷ []                                     -- Loop success

interceptASP (chs , stack) program (constraint cn ∷ goals) constraints = 
  eval interceptASP (chs , stack) program (constraint cn ∷ goals) constraints
interceptASP {Atom}{C}{Code}{Constraint} (chs , stack) program (atom (forAll v x) ∷ goals) constraints with collectVarsᵥ C Code Constraint v
interceptASP (chs , stack) program (atom (forAll v x) ∷ goals) constraints | (n ∷ _) =
  if cForall n (eval interceptASP (chs , stack) program (atom x ∷ goals) [])
  then eval interceptASP (chs , stack) program goals constraints
  else []
interceptASP (chs , stack) program (atom (forAll v x) ∷ goals) constraints | [] =
  checkASP (forAll v x) (chs , stack) program goals constraints
interceptASP (chs , stack) program (atom at ∷ goals) constraints = 
  checkASP at (chs , stack) program goals constraints
interceptASP x y [] z = 
  eval interceptASP x y [] z