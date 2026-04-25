module ASP.cforall where

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

open import Generics

open import CLP.clp
open import ASP.dual
--   cForallNested vs answers store:
--     case vs of
--       []      → either no answers needed (top-level coverage
--                 was already discharged by an outer level), or
--                 we still need every answer to confirm coverage
--                 of the residual store.  We treat [] as "no more
--                 partitioning to do" and just succeed if there
--                 are no remaining refinements.
--       v ∷ vs' → for each answer:
--                   project onto v under the current store
--                   if it covers   → record the cell, continue
--                                    with remaining answers on the
--                                    same store
--                   else            → record the cell with the
--                                    answer's projection, then
--                                    refine the store with ¬A_v,
--                                    and recurse on vs' (the inner
--                                    variables) within each refined
--                                    sub-store, using the same
--                                    answer list.  Continue with
--                                    remaining answers on the
--                                    original store afterwards.
--
-- A cell is just one Answer (asp-state + residual store), exactly
-- as before.  The output is a flat list of cells.

-- ---------------------------------------------------------------
-- 2. Specialized payload types
-- ---------------------------------------------------------------
 
private
  ASPState : ∀ {Atom 𝒞 Code Constraint} → Set
  ASPState {Atom}{𝒞}{Code}{Constraint} =
    ASPUtils Atom 𝒞 Code Constraint
    × List (ASPAtom Atom 𝒞 Code Constraint)
    × List (ASPAtom Atom 𝒞 Code Constraint)
    × List (Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
                                ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
                  × Modifier × (ASPAtom Atom 𝒞 Code Constraint)))
 
  Store : ∀ {𝒞 Code Constraint} → Set
  Store {𝒞}{Code}{Constraint} =
    (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
                  ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
 
  Answer : ∀ {Atom 𝒞 Code Constraint} → Set
  Answer {Atom}{𝒞}{Code}{Constraint} =
    ASPState {Atom}{𝒞}{Code}{Constraint} × Store {𝒞}{Code}{Constraint}
 
-- ---------------------------------------------------------------
-- 3. Single-variable partition step
--    Decompose one answer's body into (v-mentioning, non-v) parts,
--    test coverage against `store`, and either:
--      * return (covers = true,  refinement = [])
--      * return (covers = false, refinement = list of refined stores)
--    The cell to record is always the answer itself; we just need
--    to know whether to continue on the same store or recurse on
--    the refinement(s).
-- ---------------------------------------------------------------
 
private
  partitionStep :
    ∀ {Atom 𝒞 Code Constraint}
    → ⦃ DecEq 𝒞 ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ Solver 𝒞 Code Constraint ⦄
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → ℕ
    → Store {𝒞}{Code}{Constraint}
    → Answer {Atom}{𝒞}{Code}{Constraint}
    → Bool × Store {𝒞}{Code}{Constraint}
  partitionStep {Atom}{𝒞}{Code}{Constraint} v store (_ , answer) =
    let
      xy : List (List _ × List _)
      xy = Data.List.map
             (partitionᵇ (any (_≡ᵇ_ v) ∘ collectVarsᵥ {_}{⊤} 𝒞 Code Constraint))
             answer
 
      vConstraints  = Data.List.map proj₁ xy
      nonVPerBranch = Data.List.map proj₂ xy
 
      storeWithNonV : List (List _)
      storeWithNonV =
        concat (Data.List.map
                  (λ s → Data.List.map (λ nv → s ++ nv) nonVPerBranch)
                  store)
 
      branchCovers : List _ → Bool
      branchCovers vCns = all
        (λ cn → null (schedule (negateConstraint cn ∷ []) storeWithNonV))
        vCns
 
      refineStores : List _ → List (List _)
      refineStores vCns = concat (Data.List.map
        (λ cn → filterᵇ (Data.Bool.not ∘ null)
                       (schedule (negateConstraint cn ∷ []) storeWithNonV))
        vCns)
 
      covers     = any branchCovers vConstraints
      refinement = concat (Data.List.map refineStores vConstraints)
    in
    (covers , refinement)
 
-- ---------------------------------------------------------------
-- 4. Nested C-forall
--    Recursive over the variable list. Within each level, iterate
--    over the answer list. On non-coverage, recurse on the inner
--    variables within each refined sub-store.
-- ---------------------------------------------------------------
 
{-# TERMINATING #-}  -- structural recursion on (vs , answers) pairs;
                     -- Agda may need help seeing the joint decrease
cForallNested :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List ℕ
  → List (Answer {Atom}{𝒞}{Code}{Constraint})
  → Store {𝒞}{Code}{Constraint}
  → Maybe (List (Answer {Atom}{𝒞}{Code}{Constraint}))
-- No more variables to partition: every remaining answer is
-- automatically a covering cell for the residual store.  (If the
-- store were still uncovered at this point, the previous variable's
-- partition would have already failed.)
cForallNested []       _       _     = just []
-- No more answers but variables remain: the universal claim hasn't
-- been discharged on the current sub-store, so fail.
cForallNested (_ ∷ _)  []      _     = nothing
cForallNested (v ∷ vs) (an ∷ answers) store
  with partitionStep v store an
... | (true  , _)          =
      -- This answer covers v under store; record it and continue
      -- with the rest of the answers on the same store.
      cForallNested (v ∷ vs) answers store
        Data.Maybe.>>= (just ∘ (_∷_ an))
... | (false , [])         =
      -- Answer doesn't cover and there's no consistent refinement
      -- left → C-forall fails.
      nothing
... | (false , refinement) =
      -- Record this cell, then recurse on the inner variables with
      -- the same answer list under the refined store.  The
      -- refinement is already a List (List _) — the outer list is
      -- the disjunction of ¬A_v.j, the inner list is the conjunction
      -- inside each disjunct — i.e. exactly the Store shape.  Pass
      -- it through unchanged.  Then continue with the remaining
      -- answers on the *original* store.
      cForallNested vs (an ∷ answers) refinement Data.Maybe.>>= λ inner →
      cForallNested (v ∷ vs) answers store Data.Maybe.>>= λ rest →
      just (an ∷ inner ++ rest)
 
-- ---------------------------------------------------------------
-- 5. Top-level entry: same shape as your old `cForall`
-- ---------------------------------------------------------------
 
cForall :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List ℕ
  → List (Answer {Atom}{𝒞}{Code}{Constraint})
  → Maybe (List (Answer {Atom}{𝒞}{Code}{Constraint}))
cForall vs answers = cForallNested vs answers ([] ∷ [])