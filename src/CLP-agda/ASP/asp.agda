{-# OPTIONS --allow-unsolved-metas #-}

-- general top-level aggregator for asp usage

module ASP.asp where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
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

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

open import CLP.clp
open import ASP.dual
open import ASP.nmr
open import ASP.loops

-- FTUtils needs to be implemented also for ASPAtom

instance aspFT : ∀ {Atom 𝒞 Code Constraint} → ⦃ FTUtils Atom ⦄ → FTUtils (ASPAtom Atom 𝒞 Code Constraint)
         aspFT .functor (wrap at _ _) = functor at
         aspFT .functor (forAll _ _) = "forAll"
         aspFT .functor nmrCheck = "nmrCheck"
         aspFT .functor (chk _ _ _) = "chk"
         aspFT .getNat _ = nothing
         aspFT .varName _ = nothing
         aspFT {_}{C}{Code}{Constraint} .occurs n (wrap at _ x) = occurs n at ∨ occursᵥ C Code Constraint n x
         aspFT {_}{C}{Code}{Constraint} .occurs n (forAll x y) = occursᵥ C Code Constraint n x ∨ occurs n y
         aspFT .occurs n nmrCheck = false
         aspFT {_}{C}{Code}{Constraint} .occurs n (chk _ _ x) = occursᵥ C Code Constraint n x
         aspFT {_}{C}{Code}{Constraint} .collectVars (wrap at _ x) = collectVars at ++ collectVarsᵥ C Code Constraint x
         aspFT {_}{C}{Code}{Constraint} .collectVars (forAll x y) = collectVarsᵥ C Code Constraint x ++ collectVars y
         aspFT .collectVars nmrCheck = []
         aspFT {_}{C}{Code}{Constraint} .collectVars (chk _ _ x) = collectVarsᵥ C Code Constraint x

incrementExi : ∀ {𝒞 Code Constraint} → ℕ → Σᵢ 𝒞 Code Code Constraint → Σᵢ 𝒞 Code Code Constraint
incrementExi n (_:-:_ c x ⦃ _ ⦄ ⦃ val ⦄) = (_:-:_ c (increment val c n x))

zipMatchExi : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄ 
  → List (Σᵢ 𝒞 Code Code Constraint) 
  → List (Σᵢ 𝒞 Code Code Constraint) 
  → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
zipMatchExi (x ∷ xs) [] = nothing
zipMatchExi [] (x ∷ xs) = nothing
zipMatchExi [] [] = just []
zipMatchExi ((_:-:_ c₀ x ⦃ _ ⦄ ⦃ val ⦄) ∷ xs) ((_:-:_ c₁ y ⦃ _ ⦄ ⦃ _ ⦄) ∷ ys) with c₀ ≟ c₁
... | yes refl = zipMatchExi xs ys Data.Maybe.>>= (just ∘ _∷_ (_:-:_ c₀ (x =ℒ y) ⦃ _ ⦄ ⦃ val ⦄))
... | no _ = nothing

-- AtomUtils needs to be implemented for ASPAtom

instance aspAtom : ∀ {Atom 𝒞 Code Constraint} → ⦃ DecEq 𝒞 ⦄ → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄ → AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
         aspAtom {_}{C}{Code}{Constraint} ⦃ _ ⦄ ⦃ at ⦄ .zipMatch (wrap at₀ n₀ x₀) (wrap at₁ n₁ x₁) = 
          if n₀ ≡ᵇ n₁
          then zipMatch at at₀ at₁ Data.Maybe.>>= (λ y → zipMatchExi x₀ x₁ Data.Maybe.>>= (λ z → just (y ++ z)))
          else nothing
         aspAtom {_}{C}{Code}{Constraint} .zipMatch (forAll x₀ y₀) (forAll x₁ y₁) = 
          zipMatch aspAtom y₀ y₁ Data.Maybe.>>= (λ y → zipMatchExi (x₀ ∷ []) (x₁ ∷ []) Data.Maybe.>>= (λ z → just (y ++ z)))
         aspAtom .zipMatch nmrCheck nmrCheck = just []
         aspAtom {_}{C}{Code}{Constraint} ⦃ at ⦄ .zipMatch (chk a₀ b₀ x₀) (chk a₁ b₁ x₁) = 
          if (a₀ ≡ᵇ a₁) Data.Bool.∧ (b₀ ≡ᵇ b₁)
          then zipMatchExi x₀ x₁
          else nothing
         aspAtom .zipMatch _ _ = nothing
         aspAtom ⦃ _ ⦄ ⦃ att ⦄ .increment n (wrap at y x) = wrap (increment att n at) y (Data.List.map (incrementExi n) x)
         aspAtom .increment n (forAll x y) = forAll (incrementExi n x) (increment aspAtom n y)
         aspAtom .increment n nmrCheck = nmrCheck
         aspAtom .increment n (chk a b x) = chk a b (Data.List.map (incrementExi n) x)

-- ASPUtils needs to be implemented for ASPAtom

instance  aspAtomUtils : ∀ {Atom 𝒞 Code Constraint} → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄ → ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
          aspAtomUtils .ASP.types.not (wrap at a b) = wrap (ASP.types.not at) a b
          aspAtomUtils .ASP.types.not (forAll a b) = forAll a (ASP.types.not b)
          aspAtomUtils .ASP.types.not nmrCheck = nmrCheck
          aspAtomUtils .ASP.types.not (chk a b c) = chk a b c
          aspAtomUtils .isNot (wrap at _ _) = isNot at
          aspAtomUtils .isNot (forAll a b) = isNot b
          aspAtomUtils .isNot nmrCheck = false
          aspAtomUtils .isNot (chk a b c) = true
          aspAtomUtils .ASP.types.isFalse _ = false
          aspAtomUtils .toggle (wrap at a b) = wrap (toggle at) a b
          aspAtomUtils .toggle (forAll a b) = forAll a (toggle b)
          aspAtomUtils .toggle nmrCheck = nmrCheck
          aspAtomUtils .toggle (chk a b c) = chk a b c
          aspAtomUtils .fillWithVars (wrap at a b) n = wrap (fillWithVars at n) a b
          aspAtomUtils .fillWithVars (forAll a b) n = forAll a (fillWithVars b n)
          aspAtomUtils .fillWithVars nmrCheck n = nmrCheck
          aspAtomUtils .fillWithVars (chk a b c) n = chk a b c

-- Wrapper around clpExecute with parameterization for ASP-behavior. Entry point for executions of asp programs.
-- The Custom state in this case is (List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint))
-- The first list is the chs (Coinductive Hypothesis Set), and the second one is the current call stack (important for loop detection)
-- The conversion from CST to AST in this case is a concatenation of computeNMR and computeDual (nmr and dual rule synthesis)
-- The addNMR adds the nmr call to the end of the goal.
-- The intercepter is the ASPintercepter.
-- The initial chs , callstack tuple is a tuple of empty lists.
aspExecute : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → Clause Atom validate 𝒞 Code Constraint
  → Body Atom (validate bodyOfRule) 𝒞 Code Constraint
  → List ((List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint)) × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
aspExecute program goal with (toIntern  ∘ proj₂ ∘ applyVars program) 0 | toLiteralList goal
aspExecute {Atom}{C}{_}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ _ ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ asp ⦄ ⦃ x ⦄ ⦃ y ⦄ ⦃ z ⦄ program goal | internProgram | internGoal =
  clpExecute {Atom}{ASPAtom Atom C Code Constraint}
    (λ x → Data.List.map (λ y → ((λ x → wrap x 0 []) ∘ ClauseI.head) y :-- 
                          (Data.List.map (toNewLiteral (λ x → wrap x 0 [])) ∘ ClauseI.body) y) x 
    ++ computeNMR ⦃ sched ⦄ ⦃ asp ⦄ x 
    ++ computeDuals x) 
    addNMR 
    (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ asp ⦄ ⦃ x ⦄ ⦃ y ⦄)
    ([] , []) 
    internProgram 
    internGoal