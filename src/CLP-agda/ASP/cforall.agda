{-# OPTIONS --rewriting #-}
module ASP.cforall where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (equal; _≟_)
open import Data.List hiding (_++_)
open import Data.List.Base hiding (_++_)
open import Data.List.Membership.DecSetoid using (_∈?_)
open import Data.Maybe 
  using (Maybe; just; nothing; map; is-just)
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Function.Base

open import Generics

open import CLP.clp
open import CLP.outputFormatter
open import ASP.outputFormatter using (groundAtom)
open import ASP.dual

private
  ASPState : ∀ (Atom 𝒞 : Set) (Code Constraint : 𝒞 → Set) → Set
  ASPState Atom 𝒞 Code Constraint =
    ASPUtils Atom 𝒞 Code Constraint
    × List (ASPAtom Atom 𝒞 Code Constraint)
    × List (ASPAtom Atom 𝒞 Code Constraint)
    × List (Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
                                ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
                  × Modifier × (ASPAtom Atom 𝒞 Code Constraint)))
 
  Store : ∀ (𝒞 : Set) (Code Constraint : 𝒞 → Set) → Set
  Store 𝒞 Code Constraint =
    (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
 
  Conjunct : ∀ (𝒞 : Set) (Code Constraint : 𝒞 → Set) → Set
  Conjunct 𝒞 Code Constraint =
    (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)

  GroundConjunct : ∀ (𝒞 : Set) (Code Constraint : 𝒞 → Set) → Set
  GroundConjunct 𝒞 Code Constraint =
    (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint)
 
JTree : ∀ (Atom 𝒞 : Set) (Code Constraint : 𝒞 → Set) → Set
JTree Atom 𝒞 Code Constraint =
  Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
                      ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
        × Modifier × (ASPAtom Atom 𝒞 Code Constraint))

private
  -- Compute the new chs entries: those in `outChs` but not in
  -- `inChs`.  The engine prepends new entries, so the new ones
  -- are the prefix of length (|outChs| − |inChs|).
  newChsEntries :
    ∀ {Atom 𝒞 Code Constraint}
    → List (ASPAtom Atom 𝒞 Code Constraint)
    → List (ASPAtom Atom 𝒞 Code Constraint)
    → List (ASPAtom Atom 𝒞 Code Constraint)
  newChsEntries inChs outChs =
    take (length outChs ∸ length inChs) outChs

  -- Project the answer onto V: keep conjuncts that involve v
  -- AND directly relate v to a constant (not to another variable).
  projectOnOne :
    ∀ {𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ℕ
    → List (Conjunct 𝒞 Code Constraint)
    → List (Conjunct 𝒞 Code Constraint)
  projectOnOne v cns =
    filterᵇ
      (λ c →
        let vars = collectVarsᵥ {_} {⊤} _ _ _ c
        in any (_≡ᵇ v) vars Data.Bool.∧ (length vars ≡ᵇ 1))
      cns

  refineByNegation :
    ∀ {𝒞 Code Constraint}
    → ⦃ DecEq 𝒞 ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ Solver 𝒞 Code Constraint ⦄
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → List (Conjunct 𝒞 Code Constraint)
    → Store 𝒞 Code Constraint
    → List (Store 𝒞 Code Constraint)
  refineByNegation ansProj store =
    filterᵇ (Data.Bool.not ∘ null)
      (Data.List.Base.map (λ cn → schedule (negateConstraint cn ∷ []) store) ansProj)

  withChs :
    ∀ {Atom 𝒞 Code Constraint}
    → List (ASPAtom Atom 𝒞 Code Constraint)
    → ASPState Atom 𝒞 Code Constraint
    → ASPState Atom 𝒞 Code Constraint
  withChs newChs (utils , _ , stack , jts) =
    (utils , newChs , stack , jts)

  getChs :
    ∀ {Atom 𝒞 Code Constraint}
    → ASPState Atom 𝒞 Code Constraint
    → List (ASPAtom Atom 𝒞 Code Constraint)
  getChs (_ , chs , _ , _) = chs

private
  swapVarInAtom :
    ∀ {Atom 𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ atu : AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
    → Σᵢ 𝒞 Code Code Constraint
    → ℕ → ℕ
    → ASPAtom Atom 𝒞 Code Constraint
    → ASPAtom Atom 𝒞 Code Constraint
  swapVarInAtom ⦃ atu = atu ⦄
    (_:-:_ c _ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ mv ⦄ ⦃ _ ⦄ ⦃ _ ⦄) v_old v_new at =
    AtomUtils.apply atu c v_old (MakeVar.fresh mv v_new) at

  swapVarInLit :
    ∀ {𝒞 Code Constraint}
    → ⦃ vu : ValueUtils 𝒞 Code Constraint ⦄
    → (cTerm : 𝒞)
    → MakeVar (Code cTerm)
    → ℕ → ℕ
    → (cInner : 𝒞)
    → ℒ (Code cInner) → ℒ (Code cInner)
  swapVarInLit ⦃ vu = vu ⦄ cTerm mv v_old v_new cInner (a =ℒ b) =
    (ValueUtils.apply vu cTerm cInner v_old (MakeVar.fresh mv v_new) a) =ℒ
    (ValueUtils.apply vu cTerm cInner v_old (MakeVar.fresh mv v_new) b)
  swapVarInLit ⦃ vu = vu ⦄ cTerm mv v_old v_new cInner (a ≠ℒ b) =
    (ValueUtils.apply vu cTerm cInner v_old (MakeVar.fresh mv v_new) a) ≠ℒ
    (ValueUtils.apply vu cTerm cInner v_old (MakeVar.fresh mv v_new) b)

  swapVarInDual :
    ∀ {𝒞 Code Constraint}
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → (cTerm : 𝒞)
    → MakeVar (Code cTerm)
    → ℕ → ℕ
    → (cInner : 𝒞)
    → Dual (Constraint cInner) → Dual (Constraint cInner)
  swapVarInDual ⦃ cu ⦄ cTerm mv v_old v_new cInner (default cn) =
    default (ConstraintUtils.apply cu cTerm cInner v_old (MakeVar.fresh mv v_new) cn)
  swapVarInDual ⦃ cu ⦄ cTerm mv v_old v_new cInner (dual cn) =
    dual (ConstraintUtils.apply cu cTerm cInner v_old (MakeVar.fresh mv v_new) cn)

  swapVarInConjunct :
    ∀ {𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → Σᵢ 𝒞 Code Code Constraint
    → ℕ → ℕ
    → Conjunct 𝒞 Code Constraint
    → Conjunct 𝒞 Code Constraint
  swapVarInConjunct
    (_:-:_ cTerm _ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ mv ⦄ ⦃ _ ⦄ ⦃ _ ⦄)
    v_old v_new (inj₁ (_:-:_ cInner lit ⦃ a ⦄ ⦃ b ⦄ ⦃ c ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄)) =
    inj₁ (_:-:_ cInner (swapVarInLit cTerm mv v_old v_new cInner lit)
            ⦃ a ⦄ ⦃ b ⦄ ⦃ c ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄)
  swapVarInConjunct
    (_:-:_ cTerm _ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ mv ⦄ ⦃ _ ⦄ ⦃ _ ⦄)
    v_old v_new (inj₂ (_:-:_ cInner du ⦃ a ⦄ ⦃ b ⦄ ⦃ c ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄)) =
    inj₂ (_:-:_ cInner (swapVarInDual cTerm mv v_old v_new cInner du)
            ⦃ a ⦄ ⦃ b ⦄ ⦃ c ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄)

  swapVarInStore :
    ∀ {𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → Σᵢ 𝒞 Code Code Constraint
    → ℕ → ℕ
    → Store 𝒞 Code Constraint
    → Store 𝒞 Code Constraint
  swapVarInStore term v_old v_new store =
    Data.List.Base.map
      (Data.List.Base.map (swapVarInConjunct term v_old v_new))
      store

{-# TERMINATING #-}
cForallExec :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List (Σᵢ 𝒞 Code Code Constraint × ℕ)
  → ASPAtom Atom 𝒞 Code Constraint
  → ( ASPAtom Atom 𝒞 Code Constraint
    → ℕ
    → ASPState Atom 𝒞 Code Constraint
    → Store 𝒞 Code Constraint
    → List (ℕ × ASPState Atom 𝒞 Code Constraint × Store 𝒞 Code Constraint) )
  → ℕ                                  -- input counter
  → ASPState Atom 𝒞 Code Constraint
  → Store 𝒞 Code Constraint
  → Maybe ( ℕ                          -- new counter
          × ASPState Atom 𝒞 Code Constraint
          × Store 𝒞 Code Constraint
          × List (JTree Atom 𝒞 Code Constraint) )

{-# TERMINATING #-}
descendCells :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → Σᵢ 𝒞 Code Code Constraint
  → ℕ
  → List (Σᵢ 𝒞 Code Code Constraint × ℕ)
  → ASPAtom Atom 𝒞 Code Constraint
  → ( ASPAtom Atom 𝒞 Code Constraint
    → ℕ
    → ASPState Atom 𝒞 Code Constraint
    → Store 𝒞 Code Constraint
    → List (ℕ × ASPState Atom 𝒞 Code Constraint × Store 𝒞 Code Constraint) )
  → ℕ                                  -- input counter
  → ASPState Atom 𝒞 Code Constraint
  → Store 𝒞 Code Constraint                    -- threaded store from prior cells
  → List (Conjunct 𝒞 Code Constraint)          -- list of refinement-conjuncts (one per pending cell)
  → Maybe ( ℕ                                  -- new counter
          × ASPState Atom 𝒞 Code Constraint
          × Store 𝒞 Code Constraint
          × List (JTree Atom 𝒞 Code Constraint) )
descendCells term v_old rest body evalGoal n state threadedStore [] =
  just (n , state , threadedStore , [])
descendCells term v_old rest body evalGoal n state threadedStore (refinement ∷ moreRefinements) =
  -- Allocate fresh NV directly from the threaded counter — no
  -- need to walk body/chs/store any more.
  let v_new       = suc n
      n′          = v_new                     -- bumped counter; this NV is now in scope
      renamedBody = swapVarInAtom term v_old v_new body
      -- Apply this cell's refinement, with v_old → v_new
      -- (so the refinement constrains THIS cell's NV, not prior
      -- cells' NVs).
      renamedRefinement = swapVarInConjunct term v_old v_new refinement
      -- Build cell N+1's input store: take threaded store from
      -- prior cells, add this cell's refinement.  Run schedule
      -- to normalize.
      cellInputCandidates = schedule (renamedRefinement ∷ []) threadedStore
  in case cellInputCandidates of λ where
       [] →
         -- This cell's refinement is inconsistent with the
         -- threaded store; skip this cell.
         descendCells term v_old rest body evalGoal n state threadedStore moreRefinements
       cellInputStore →
         case (cForallExec rest renamedBody evalGoal n′ state cellInputStore) of λ where
             nothing →
               nothing
             (just (nAfter , stateAfterHere , storeAfterHere , cellsHere)) →
               case (descendCells term v_old rest body evalGoal nAfter stateAfterHere storeAfterHere moreRefinements) of λ where
                   nothing →
                     nothing
                   (just (nFinal , finalState , finalStore , cellsRest)) →
                     just (nFinal , finalState , finalStore ,
                           Data.List.Base._++_ cellsHere cellsRest)

cForallExec [] body evalGoal n state store
  with evalGoal body n state store
... | [] =
  nothing
... | ((nNew , newState , cellStore) ∷ _) =
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
      (_ , _ , _ , nJust) = newState
  in just (nNew , threaded , cellStore , nJust)

cForallExec ((term , v) ∷ rest) body evalGoal n state store
  with evalGoal body n state store
... | [] =
  nothing
... | ((nNew , newState , []) ∷ _) =
  -- Empty residual: head call succeeded with no constraints.
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
      (_ , _ , _ , nJust) = newState
  in just (nNew , threaded , [] , nJust)
... | ((nNew , newState@(_ , _ , _ , nJust) , cellStore@(ansConj ∷ _)) ∷ _)
  with projectOnOne v ansConj
... | [] =
  -- v unconstrained on this branch.
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
  in just (nNew , threaded , cellStore , nJust)
... | ansProj =
  -- For each conjunct in the projection, the "refinement" is its
  -- negation (the dual).  We pass the list of NEGATED-conjuncts
  -- to descendCells, which will rename + schedule each per cell.
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
      negatedConjuncts = Data.List.Base.map negateConstraint ansProj
  in case (descendCells term v rest body evalGoal nNew threaded
                        cellStore   -- start threaded store from head call's residual
                        negatedConjuncts) of λ where
       nothing →
         nothing
       (just (nFinal , finalState , finalStore , descendedCells)) →
         just (nFinal , finalState , finalStore ,
               Data.List.Base._++_ nJust descendedCells)