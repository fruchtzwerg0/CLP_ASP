-- general top-level aggregator for asp usage

module ASP.asp where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
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
open import ASP.outputFormatter

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
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ Show Atom ⦄
  → Clause Atom validate 𝒞 Code Constraint
  → Body Atom (validate bodyOfRule) 𝒞 Code Constraint
  → List String
aspExecute {Atom}{C}{_}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ at ⦄ ⦃ as ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄ ⦃ sho ⦄ program goal with (toIntern  ∘ proj₂ ∘ applyVars program) 0 | toLiteralList goal
aspExecute {Atom}{C}{_}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ at ⦄ ⦃ as ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄ ⦃ sho ⦄ program goal | internProgram | internGoal =
  (Data.List.map aspFormat ∘ clpExecute {Atom}{ASPAtom Atom C Code Constraint} ⦃ dec ⦄ ⦃ aspFT ⦃ ft ⦄ ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄
    (λ x → Data.List.map (λ y → _:--_ ((toNewAtom ⦃ ClauseI.instAt y ⦄ ∘ ClauseI.head) y)
                          (Data.List.map (toNewLiteral ⦃ aspFT ⦃ ft ⦄ ⦄ ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄ (toNewAtom ⦃ ClauseI.instAt y ⦄)) (ClauseI.body y))
                          ⦃ aspFT ⦃ ft ⦄ ⦄ ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄) x 
    ++ computeNMR ⦃ cns ⦄ ⦃ val ⦄ ⦃ as ⦄ ⦃ aspAtomUtils ⦃ as ⦄ ⦄ ⦃ aspFT ⦃ ft ⦄ ⦄ ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄ ⦃ at ⦄ ⦃ dec ⦄ x 
    ++ computeDuals ⦃ as ⦄ ⦃ at ⦄ ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄ ⦃ val ⦄ ⦃ aspAtomUtils ⦃ as ⦄ ⦄ ⦃ cns ⦄ ⦃ aspFT ⦃ ft ⦄ ⦄ ⦃ dec ⦄ x) 
    (addNMR ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄ ⦃ aspFT ⦃ ft ⦄ ⦄)
    (interceptASP ⦃ dec ⦄ ⦃ aspFT ⦃ ft ⦄ ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ aspAtom ⦃ dec ⦄ ⦃ at ⦄ ⦃ val ⦄ ⦄ ⦃ solv ⦄ ⦃ sched ⦄)
    true
    (as , sho ,  [] , [] , "") 
    internProgram) 
    internGoal