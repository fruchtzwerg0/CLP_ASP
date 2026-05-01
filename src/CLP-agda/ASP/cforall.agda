{-# OPTIONS --rewriting #-}
module ASP.cforall where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Data.Bool hiding (_≟_)
open import Data.String 
  using (String; _++_; _==_)
open import Data.Nat hiding (equal; _≟_)
open import Data.Nat.Show using () renaming (show to showℕ)
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
open import Debug.Trace

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
  showVarList : List ℕ → String
  showVarList []       = "[]"
  showVarList (v ∷ vs) = "[" ++ showℕ v ++ go vs ++ "]"
    where
      go : List ℕ → String
      go []       = ""
      go (x ∷ xs) = "," ++ showℕ x ++ go xs

  showConjunct :
    ∀ {𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → Conjunct 𝒞 Code Constraint
    → String
  showConjunct (inj₁ c@(_ :-: (_ =ℒ _))) = "Eq"  ++ showVarList (collectVarsᵥ {_} {⊤} _ _ _ (inj₁ c))
  showConjunct (inj₁ c@(_ :-: (_ ≠ℒ _))) = "Neq" ++ showVarList (collectVarsᵥ {_} {⊤} _ _ _ (inj₁ c))
  showConjunct (inj₂ c)                  = "Dual" ++ showVarList (collectVarsᵥ {_} {⊤} _ _ _ (inj₂ c))

  showConjunctList :
    ∀ {𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → List (Conjunct 𝒞 Code Constraint)
    → String
  showConjunctList []       = "{}"
  showConjunctList (c ∷ cs) = "{" ++ showConjunct c ++ go cs ++ "}"
    where
      go : ∀ {𝒞 Code Constraint} → ⦃ ValueUtils 𝒞 Code Constraint ⦄
        → List (Conjunct 𝒞 Code Constraint) → String
      go []       = ""
      go (x ∷ xs) = ", " ++ showConjunct x ++ go xs

  showStore :
    ∀ {𝒞 Code Constraint}
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → Store 𝒞 Code Constraint
    → String
  showStore []           = "[]"
  showStore (cs ∷ rest)  = "[" ++ showConjunctList cs ++ go rest ++ "]"
    where
      go : ∀ {𝒞 Code Constraint} → ⦃ ValueUtils 𝒞 Code Constraint ⦄
        → Store 𝒞 Code Constraint → String
      go []          = ""
      go (cs ∷ rest) = " ; " ++ showConjunctList cs ++ go rest

private
  newChsEntries :
    ∀ {Atom 𝒞 Code Constraint}
    → List (ASPAtom Atom 𝒞 Code Constraint)
    → List (ASPAtom Atom 𝒞 Code Constraint)
    → List (ASPAtom Atom 𝒞 Code Constraint)
  newChsEntries inChs outChs =
    take (length outChs ∸ length inChs) outChs

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

  -- Compute max var id across an atom + chs + store.
  maxVarInScope :
    ∀ {Atom 𝒞 Code Constraint}
    → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ASPAtom Atom 𝒞 Code Constraint
    → List (ASPAtom Atom 𝒞 Code Constraint)
    → Store 𝒞 Code Constraint
    → ℕ
  maxVarInScope at chs store =
    foldr _⊔_ 0
      (collectVars at Data.List.Base.++
       (concat (Data.List.Base.map collectVars chs)) Data.List.Base.++
       (concat (Data.List.Base.map (λ d →
          concat (Data.List.Base.map (collectVarsᵥ {_} {⊤} _ _ _) d)) store)))

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
    → ASPState Atom 𝒞 Code Constraint
    → Store 𝒞 Code Constraint
    → List (ASPState Atom 𝒞 Code Constraint × Store 𝒞 Code Constraint) )
  → ASPState Atom 𝒞 Code Constraint
  → Store 𝒞 Code Constraint
  → Maybe ( ASPState Atom 𝒞 Code Constraint
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
    → ASPState Atom 𝒞 Code Constraint
    → Store 𝒞 Code Constraint
    → List (ASPState Atom 𝒞 Code Constraint × Store 𝒞 Code Constraint) )
  → ASPState Atom 𝒞 Code Constraint
  → Store 𝒞 Code Constraint
  → List (Conjunct 𝒞 Code Constraint)
  → Maybe ( ASPState Atom 𝒞 Code Constraint
          × Store 𝒞 Code Constraint
          × List (JTree Atom 𝒞 Code Constraint) )
descendCells term v_old rest body evalGoal state threadedStore [] =
  trace "[descendCells] base case: empty refinement list"
    (just (state , threadedStore , []))
descendCells term v_old rest body evalGoal state threadedStore (refinement ∷ moreRefinements) =
  -- Allocate fresh NV from the threaded store + chs + body.
  let mark        = maxVarInScope body (getChs state) threadedStore
      v_new       = suc mark
      renamedBody = swapVarInAtom term v_old v_new body
      renamedRefinement = swapVarInConjunct term v_old v_new refinement
      cellInputCandidates = schedule (renamedRefinement ∷ []) threadedStore
  in case cellInputCandidates of λ where
       [] →
         -- This cell's refinement is inconsistent with the
         -- threaded store; skip this cell.  This shouldn't
         -- normally happen after refineByNegation already
         -- filtered, but be defensive.
         trace ("[descendCells] cell with v_old=" ++ showℕ v_old ++
                " v_new=" ++ showℕ v_new ++
                ": refinement inconsistent with threaded store; skipping")
           (descendCells term v_old rest body evalGoal state threadedStore moreRefinements)
       cellInputStore →
         case (trace ("[descendCells] cell with v_old=" ++ showℕ v_old ++
                      " v_new=" ++ showℕ v_new ++
                      "; cellInputStore=" ++ showStore cellInputStore ++
                      "; chs len=" ++ showℕ (length (getChs state)))
               (cForallExec rest renamedBody evalGoal state cellInputStore)) of λ where
             nothing →
               trace "[descendCells] cForallExec failed; bailing" nothing
             (just (stateAfterHere , storeAfterHere , cellsHere)) →
               case (trace ("[descendCells] cell done; recursing on " ++
                            showℕ (length moreRefinements) ++ " more, " ++
                            "storeAfterHere=" ++ showStore storeAfterHere)
                     (descendCells term v_old rest body evalGoal stateAfterHere storeAfterHere moreRefinements)) of λ where
                   nothing →
                     trace "[descendCells] subsequent cells failed; bailing" nothing
                   (just (finalState , finalStore , cellsRest)) →
                     trace ("[descendCells] returning " ++
                            showℕ (length cellsHere) ++ " + " ++
                            showℕ (length cellsRest) ++ " cells")
                       (just (finalState , finalStore ,
                              Data.List.Base._++_ cellsHere cellsRest))

-- Leaf case: no more forall variables.
cForallExec [] body evalGoal state store
  with trace ("[cForallExec []] CALL inChs=" ++ showℕ (length (getChs state)) ++
              " store=" ++ showStore store)
       (evalGoal body state store)
... | [] =
  trace "[cForallExec []] evalGoal returned EMPTY; failing"
    nothing
... | ((newState , cellStore) ∷ _) =
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
      (_ , _ , _ , nJust) = newState
  in trace ("[cForallExec []] added " ++ showℕ (length addedRaw) ++
            " chs entries; threadedChs len=" ++ showℕ (length threadedChs) ++
            "; got " ++ showℕ (length nJust) ++ " trees; cellStore=" ++
            showStore cellStore)
       (just (threaded , cellStore , nJust))

-- Recursive case: peel off the next forall variable.
cForallExec ((term , v) ∷ rest) body evalGoal state store
  with trace ("[cForallExec (" ++ showℕ v ++ "∷..)] HEAD CALL inChs=" ++
              showℕ (length (getChs state)) ++ " store=" ++ showStore store)
       (evalGoal body state store)
... | [] =
  trace "[cForallExec (v∷vs)] evalGoal returned EMPTY; failing"
    nothing
... | ((newState , []) ∷ _) =
  -- Empty residual: head call succeeded with no constraints.
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
      (_ , _ , _ , nJust) = newState
  in trace ("[cForallExec (v∷vs)] EMPTY residual; returning " ++
            showℕ (length nJust) ++ " cells (head)")
       (just (threaded , [] , nJust))
... | ((newState@(_ , _ , _ , nJust) , cellStore@(ansConj ∷ _)) ∷ _)
  with trace ("[cForallExec (v∷vs)] residualStore=" ++ showStore cellStore ++
              ", first conj=" ++ showConjunctList ansConj ++
              "; nJust has " ++ showℕ (length nJust) ++ " trees")
       (projectOnOne v ansConj)
... | [] =
  -- v unconstrained on this branch.
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
  in trace ("[cForallExec (v∷vs)] projectOnOne v=" ++ showℕ v ++
            " produced EMPTY; returning " ++ showℕ (length nJust) ++ " cells (head)")
       (just (threaded , cellStore , nJust))
... | ansProj =
  let inChs       = getChs state
      newChs      = getChs newState
      addedRaw    = newChsEntries inChs newChs
      threadedChs = Data.List.Base._++_ addedRaw inChs
      threaded    = withChs threadedChs state
      negatedConjuncts = Data.List.Base.map negateConstraint ansProj
  in case (trace ("[cForallExec (v∷vs)] ansProj has " ++
                  showℕ (length ansProj) ++
                  " conjuncts; descending into cells with per-cell rename")
           (descendCells term v rest body evalGoal threaded
                         cellStore   -- start threaded store from head call's residual
                         negatedConjuncts)) of λ where
       nothing →
         trace "[cForallExec (v∷vs)] descendCells FAILED" nothing
       (just (finalState , finalStore , descendedCells)) →
         trace ("[cForallExec (v∷vs)] head produced " ++
                showℕ (length nJust) ++ " cells, descents " ++
                showℕ (length descendedCells) ++
                "; finalStore=" ++ showStore finalStore)
           (just (finalState , finalStore ,
                  Data.List.Base._++_ nJust descendedCells))