-- =============================================================
-- Direct simulation of the forall call in:
--   not other_color(1, red)
--     not o_other_color_1(1, red)
--       forall(Var2, not o_other_color_1(1, red, Var2))
-- =============================================================
--
-- We hand-build the four Answer values that the body of
--   not o_other_color_1(1, red, Var2)
-- produces, then feed them to cForallNested with Var2's variable
-- number.  The result should be four cells matching the trace.

module Examples.simulateForall where

open import Agda.Builtin.Int
open import Data.Bool hiding (_≟_ ; _∧_ ; not)
open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Unit hiding (_≟_)
open import Function.Base

open import CLP.types
open import CLP.unifyDisunify
open import CLP.solverScheduler
open import CLP.clp
open import String.domain
open import FD.domain

open import ASP.types
open import ASP.asp
open import ASP.dual
open import ASP.cforall

open import Examples.myDomainGroup
open import Examples.graphColoring

open import CLP.utilities

-- The variable number used for Var2 inside the forall.  Pick any
-- number that doesn't clash with the constants/positions in the
-- atoms.  Following s(CASP)'s convention of using fresh numbers
-- like _37406, we'll just use, say, 100.
forallVar : ℕ
forallVar = 100

-- ---------------------------------------------------------------
-- The four answers as their constraint stores (only the part
-- that mentions Var2; the body's positive lookups like
-- `color(red)` don't add constraints, and any constraints on
-- other variables are dropped because they don't affect Var2's
-- partition.)
--
-- Answer A1 (clause 2):  Var2 \= red ∧ Var2 \= green ∧ Var2 \= yellow
-- Answer A2 (clause 3):  Var2 = red
-- Answer A3 (clause 4):  Var2 = green     (with not color(1,green) succeeding)
-- Answer A4 (clause 4):  Var2 = yellow    (with not color(1,yellow) succeeding)
-- ---------------------------------------------------------------

-- Store for clause 2:  Var2 \= red,  Var2 \= green,  Var2 \= yellow
-- All three disequalities live in ONE conjunction (one inner list),
-- so the Store is a single-element outer list.
storeA1 : (List ∘ List) ((Σᵢ My𝒞 (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ)
                       ⊎ (Σᵢ My𝒞 (Dual ∘ ⟦_⟧ℒ) ⟦_⟧ ⟦_⟧ℒ))
storeA1 = ( inj₁ (string𝒞 :-: (varString forallVar ≠ℒ (~ "red")))
          ∷ inj₁ (string𝒞 :-: (varString forallVar ≠ℒ (~ "green")))
          ∷ inj₁ (string𝒞 :-: (varString forallVar ≠ℒ (~ "yellow")))
          ∷ []) ∷ []

-- Store for clause 3:  Var2 = red
storeA2 : (List ∘ List) ((Σᵢ My𝒞 (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ)
                       ⊎ (Σᵢ My𝒞 (Dual ∘ ⟦_⟧ℒ) ⟦_⟧ ⟦_⟧ℒ))
storeA2 = ( inj₁ (string𝒞 :-: (varString forallVar =ℒ (~ "red")))
          ∷ []) ∷ []

-- Store for clause 4 with Var2 = green
storeA3 : (List ∘ List) ((Σᵢ My𝒞 (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ)
                       ⊎ (Σᵢ My𝒞 (Dual ∘ ⟦_⟧ℒ) ⟦_⟧ ⟦_⟧ℒ))
storeA3 = ( inj₁ (string𝒞 :-: (varString forallVar =ℒ (~ "green")))
          ∷ []) ∷ []

-- Store for clause 4 with Var2 = yellow
storeA4 : (List ∘ List) ((Σᵢ My𝒞 (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ)
                       ⊎ (Σᵢ My𝒞 (Dual ∘ ⟦_⟧ℒ) ⟦_⟧ ⟦_⟧ℒ))
storeA4 = ( inj₁ (string𝒞 :-: (varString forallVar =ℒ (~ "yellow")))
          ∷ []) ∷ []

-- ---------------------------------------------------------------
-- The asp-state component of each Answer.  For a hand-built
-- simulation we only need the justification field to reconstruct
-- the printed tree; the other fields are placeholders.
-- ---------------------------------------------------------------

-- A trivial empty asp-state.  The justification is the tree that
-- would be produced by evaluating that one dual clause's body.
-- For the simulation we leave it as [] and just verify that
-- cForallNested's partitioning is correct.
emptyState :
  ASPUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
  × List (ASPAtom Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ)
  × List (ASPAtom Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ)
  × List (Tree ((List ∘ List) ((Σᵢ My𝒞 (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ)
                              ⊎ (Σᵢ My𝒞 (Dual ∘ ⟦_⟧ℒ) ⟦_⟧ ⟦_⟧ℒ))
                × Modifier × ASPAtom Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ))
emptyState = aspUtils , [] , [] , []

-- Each Answer = (asp-state , store).
answers :
  List ( (ASPUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
        × List (ASPAtom Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ)
        × List (ASPAtom Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ)
        × List _)
       × (List ∘ List) ((Σᵢ My𝒞 (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ)
                       ⊎ (Σᵢ My𝒞 (Dual ∘ ⟦_⟧ℒ) ⟦_⟧ ⟦_⟧ℒ)))
answers = (emptyState , storeA1)
        ∷ (emptyState , storeA2)
        ∷ (emptyState , storeA3)
        ∷ (emptyState , storeA4)
        ∷ []

-- ---------------------------------------------------------------
-- Run cForallNested on the four answers, partitioning Var2.
-- Should return a Just with four cells covering the domain.
-- ---------------------------------------------------------------

simulate = cForallNested (forallVar ∷ []) answers ([] ∷ [])