module CLP.unifyDisunify where

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.List
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤)
open import Function.Base

import Data.Tree.AVL.Map <-strictTotalOrder as Map
open Map using (Map)

open import CLP.types hiding (_∧_)
open import CLP.ftUtilsDerivation
open import CLP.utilities

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

----------------------------------------------------------------------
-- Small helpers
----------------------------------------------------------------------

decToBool : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

-- Equality on Code c via the DecEq instance
eqCode : ∀ {c : Set} {Code : c → Set} {witness : c}
       → ⦃ DecEq (Code witness) ⦄
       → Code witness → Code witness → Bool
eqCode x y = decToBool (x ≟ y)

-- membership with custom equality
memBy : {A : Set} → (A → A → Bool) → A → List A → Bool
memBy _  _ []       = false
memBy eq x (y ∷ ys) = if eq x y then true else memBy eq x ys

-- insert-if-absent
consUniq : {A : Set} → (A → A → Bool) → A → List A → List A
consUniq eq x xs = if memBy eq x xs then xs else x ∷ xs

-- dedup-append (left-biased)
unionBy : {A : Set} → (A → A → Bool) → List A → List A → List A
unionBy eq []       ys = ys
unionBy eq (x ∷ xs) ys =
  if memBy eq x ys then unionBy eq xs ys else x ∷ unionBy eq xs ys

----------------------------------------------------------------------
-- Store
----------------------------------------------------------------------

-- A variable is either bound to a term, or "attributed" with a list
-- of prohibited values and a list of suspended-dif partner variable ids.
-- Unbound variables are simply absent from the map.
data Binding {𝒞 : Set} (Code : 𝒞 → Set) (c : 𝒞) : Set where
  bound : Code c → Binding Code c
  attr  : List (Code c)   -- prohibited values
        → List ℕ          -- suspended-dif partners (other var ids)
        → Binding Code c

Store : ∀ {𝒞 : Set} → (Code : 𝒞 → Set) → 𝒞 → Set
Store Code c = Map (Binding Code c)

emptyStore : ∀ {𝒞 Code} {c : 𝒞} → Store Code c
emptyStore = Map.empty

----------------------------------------------------------------------
-- find / walk
----------------------------------------------------------------------

-- Follow `bound` pointers at the top level. Since we allow cycles
-- (no occurs check), we bound the walk by a fuel parameter equal to
-- the current store size — enough to guarantee termination without
-- expensive cycle detection on every walk.
{-# TERMINATING #-}
walk₀ : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞}
      → ⦃ FTUtils (Code c) ⦄
      → ℕ                      -- fuel
      → Store Code c
      → Code c
      → Code c
walk₀ zero    _     t = t
walk₀ (suc f) store t with varName t
... | nothing = t
... | just n  with Map.lookup store n
...   | just (bound t′) = walk₀ f store t′
...   | _               = t

walk : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞}
     → ⦃ FTUtils (Code c) ⦄
     → Store Code c
     → Code c
     → Code c
walk store t = walk₀ (suc (Map.size store)) store t

----------------------------------------------------------------------
-- The worklist item type is just ℒ (Code c) — reusing your existing
-- sum of _=ℒ_ / _≠ℒ_.
----------------------------------------------------------------------

-- A step result: a list of branches, each branch being
--   (new worklist items to add , cross-solver residual passthrough , new store)
-- An empty outer list means this step failed.
StepResult :
    ∀ {𝒞 : Set} (Code Constraint : 𝒞 → Set) (c : 𝒞) → Set
StepResult {𝒞} Code Constraint c =
  List ( List ((ℒ ∘ Code) c)
       × List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
             ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
       × Store Code c )

----------------------------------------------------------------------
-- "Can these two terms possibly unify?" — a lightweight check used
-- at bind time to rule out prohibited values.
--
-- Conservative: returns true when they *might* unify. A ground-ground
-- case reduces to structural equality; a var on either side trivially
-- could unify; a compound-compound case recurses via zipMatch.
----------------------------------------------------------------------

{-# TERMINATING #-}
canUnify :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ vu : ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ FTUtils (Code c) ⦄
  → Code c → Code c → Bool
canUnify {𝒞}{Code}{Constraint} c ⦃ decc ⦄ ⦃ vu ⦄ x y
  with varName x | varName y
... | just _  | _       = true
... | _       | just _  = true
... | nothing | nothing =
  if eqCode {c = 𝒞} {Code = Code} {witness = c} x y
  then true
  else (case ValueUtils.zipMatch vu c x y of λ where
          nothing  → false
          (just children) →
            -- only inspect children that belong to this solver
            allChildrenUnify children)
  where
    -- We can only meaningfully check children that belong to *this*
    -- solver (same 𝒞). For cross-solver children we conservatively
    -- assume they could unify (return true for that child).
    allChildrenUnify :
        List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) → Bool
    allChildrenUnify []       = true
    allChildrenUnify (ch ∷ chs) =
      -- We don't have getPermission in scope here generically; the
      -- safe conservative answer is "could unify" (true) unless the
      -- child is obviously this solver's and obviously fails. We
      -- defer to a pessimistic default: assume true.
      allChildrenUnify chs

----------------------------------------------------------------------
-- Check whether a term is allowed against a prohibited list.
-- Returns true iff the term does NOT (possibly) unify with any entry.
----------------------------------------------------------------------
checkProhibited :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ FTUtils (Code c) ⦄
  → Code c → List (Code c) → Bool
checkProhibited c t []       = true
checkProhibited c t (p ∷ ps) =
  if canUnify c t p then false else checkProhibited c t ps

----------------------------------------------------------------------
-- Bind: attempt to bind variable n to term t in the store.
-- Runs prohibited-value checks, wakes suspended difs.
-- Returns `nothing` on failure, or `just (newWorklist , newStore)`
-- where newWorklist contains suspended difs that need reprocessing.
----------------------------------------------------------------------

bindVar :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ℕ → Code c
  → Store Code c
  → Maybe (List ((ℒ ∘ Code) c) × Store Code c)
bindVar {𝒞}{Code}{Constraint} c ⦃ decc ⦄ ⦃ vu ⦄ ⦃ deccode ⦄ ⦃ mv ⦄ n t store
  with Map.lookup store n
... | just (bound _) =
  -- Shouldn't happen if caller walked first, but treat as success.
  just ([] , store)
... | just (attr prohibited suspended) =
  if not (checkProhibited c t prohibited)
  then nothing
  else
    let store′ = Map.insert n (bound t) store
        -- Wake all suspended difs involving this variable:
        -- reconstruct (var n ≠ℒ var m) for each partner m.
        wakeOps = Data.List.map (λ m → fresh n ≠ℒ fresh m) suspended
    in just (wakeOps , store′)
... | nothing =
  just ([] , Map.insert n (bound t) store)

----------------------------------------------------------------------
-- addProhibited: add a ground-ish prohibited value to variable n.
-- Fails if n is already bound to something that matches t.
----------------------------------------------------------------------

addProhibited :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ℕ → Code c
  → Store Code c
  → Maybe (Store Code c)
addProhibited {𝒞}{Code}{Constraint} c n t store
  with Map.lookup store n
... | just (bound t′) =
  -- Already bound. The dif holds iff t′ cannot possibly equal t.
  if canUnify c t′ t then nothing else just store
... | just (attr ps ss) =
  just (Map.insert n
         (attr (consUniq (λ x y → eqCode {c = 𝒞} {Code = Code} {witness = c} x y) t ps) ss)
         store)
... | nothing =
  just (Map.insert n (attr (t ∷ []) []) store)

----------------------------------------------------------------------
-- suspendDif: suspend a dif(var n, var m) by linking both ways.
----------------------------------------------------------------------

addSuspended : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞} → ℕ → ℕ
             → Store Code c → Store Code c
addSuspended n m store with Map.lookup store n
... | just (bound _)     = store   -- caller should have walked
... | just (attr ps ss)  =
  Map.insert n (attr ps (if any (λ k → k ≡ᵇ m) ss then ss else m ∷ ss)) store
... | nothing            = Map.insert n (attr [] (m ∷ [])) store

suspendDif : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞} → ℕ → ℕ → Store Code c → Store Code c
suspendDif n m store = addSuspended m n (addSuspended n m store)

----------------------------------------------------------------------
-- Partition zipMatch children: the ones belonging to *this* solver
-- get unwrapped into ℒ (Code c) for the worklist, and the ones
-- belonging to other solvers go into the passthrough residual.
----------------------------------------------------------------------

partitionChildren :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
  → List ((ℒ ∘ Code) c)
  × List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
        ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
partitionChildren c []       = [] , []
partitionChildren c (x ∷ xs) =
  let mine , others = partitionChildren c xs in
  -- Use getPermission to check if this child belongs to solver c.
  case getPermission c (inj₁ x) of λ where
    (just (inj₁ eq)) → (eq ∷ mine) , others
    _                → mine , (inj₁ x ∷ others)

----------------------------------------------------------------------
-- step: process a single ℒ-operation against the store.
--
-- Returns a StepResult: a list of branches. Empty = failure.
-- Each branch is (newOps , passthroughResidual , newStore).
-- Single-branch successes are the common case; compound-compound
-- disunification is the only source of multi-branch results.
----------------------------------------------------------------------

step :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ vu : ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → (ℒ ∘ Code) c
  → Store Code c
  → StepResult Code Constraint c
step {𝒞}{Code}{Constraint} c ⦃ _ ⦄ ⦃ _ ⦄ ⦃ vu ⦄ op store with op
... | l =ℒ r =
  let l′ = walk store l
      r′ = walk store r
  in handleUnify l′ r′
  where
    handleUnify : Code c → Code c → StepResult Code Constraint c
    handleUnify a b with varName a | varName b
    -- both variables: union them
    ... | just n | just m =
      if n ≡ᵇ m
        then ([] , [] , store) ∷ []
        else
          -- Merge: pick n as representative, redirect m to n.
          -- Merge attributes.
          (case (Map.lookup store n , Map.lookup store m) of λ where
            (just (attr pn sn) , just (attr pm sm)) →
              let eqv = λ x y → eqCode {c = 𝒞} {Code = Code} {witness = c} x y
                  mergedP = unionBy eqv pn pm
                  mergedS = unionBy (λ x y → x ≡ᵇ y)
                              (filterᵇ (λ k → not (k ≡ᵇ m)) sn)
                              (filterᵇ (λ k → not (k ≡ᵇ n)) sm)
                  store₁ = Map.insert n (attr mergedP mergedS) store
                  store₂ = Map.insert m (bound a) store₁
                  -- Wake merged suspensions by reconstructing ops.
                  wakeOps = Data.List.map (λ k → fresh n ≠ℒ fresh k) mergedS
              in (wakeOps , [] , store₂) ∷ []
            (just (attr pn sn) , _) →
              -- m is either unbound or was just-in-case bound; treat as unbound
              let store₁ = Map.insert m (bound a) store
                  wakeOps = Data.List.map (λ k → fresh n ≠ℒ fresh k) sn
              in (wakeOps , [] , store₁) ∷ []
            (_ , just (attr pm sm)) →
              let store₁ = Map.insert n (attr pm sm) store
                  store₂ = Map.insert m (bound a) store₁
                  wakeOps = Data.List.map (λ k → fresh n ≠ℒ fresh k) sm
              in (wakeOps , [] , store₂) ∷ []
            (_ , _) →
              ([] , [] , Map.insert m (bound a) store) ∷ [])
    -- left var, right non-var: bind
    ... | just n | nothing =
      case bindVar c n b store of λ where
        nothing             → []
        (just (wake , st′)) → (wake , [] , st′) ∷ []
    -- right var, left non-var: bind
    ... | nothing | just m =
      case bindVar c m a store of λ where
        nothing             → []
        (just (wake , st′)) → (wake , [] , st′) ∷ []
    -- both non-var: decompose via zipMatch
    ... | nothing | nothing =
      case ValueUtils.zipMatch vu c a b of λ where
        nothing         → []     -- clash
        (just children) →
          let mine , others = partitionChildren c children
          in (mine , others , store) ∷ []

... | l ≠ℒ r =
  let l′ = walk store l
      r′ = walk store r
  in handleDisunify l′ r′
  where
    handleDisunify : Code c → Code c → StepResult Code Constraint c
    handleDisunify a b with varName a | varName b
    -- both variables
    ... | just n | just m =
      if n ≡ᵇ m
        then []     -- X ≠ X fails
        else ([] , [] , suspendDif n m store) ∷ []
    -- var ≠ term: add to prohibited list
    ... | just n | nothing =
      case addProhibited c n b store of λ where
        nothing     → []
        (just st′)  → ([] , [] , st′) ∷ []
    -- term ≠ var: symmetric
    ... | nothing | just m =
      case addProhibited c m a store of λ where
        nothing     → []
        (just st′)  → ([] , [] , st′) ∷ []
    -- both non-var: nondet decompose
    ... | nothing | nothing =
      case ValueUtils.zipMatch vu c a b of λ where
        nothing →
          -- Functor/arity mismatch → deterministic success, no new info
          ([] , [] , store) ∷ []
        (just children) →
          -- Nondeterministic: produce one branch per child, where
          -- that child's equation is *disunified* instead of unified.
          -- Other children are irrelevant in that branch.
          let mine , others = partitionChildren c children
          in makeBranches mine others
      where
        flipOp : (ℒ ∘ Code) c → (ℒ ∘ Code) c
        flipOp (x =ℒ y) = x ≠ℒ y
        flipOp (x ≠ℒ y) = x =ℒ y

        -- For each "mine" child, produce a branch where that child's
        -- equation is negated. The `others` passthrough is duplicated
        -- across branches (same semantics as the current code).
        makeBranches :
            List ((ℒ ∘ Code) c)
          → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
                ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
          → StepResult Code Constraint c
        makeBranches []       _      = []
        makeBranches (x ∷ xs) others =
          (flipOp x ∷ [] , others , store)
          ∷ makeBranches xs others

----------------------------------------------------------------------
-- Worklist driver: process ops until empty, across all branches.
----------------------------------------------------------------------

{-# TERMINATING #-}
solveWorklist :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ℕ                                              -- fuel (debug)
  → List ((ℒ ∘ Code) c)                            -- worklist
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
        ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) -- accumulated passthrough
  → Store Code c
  → List ( List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
               ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
         × Store Code c )
solveWorklist c zero     _   passthrough store = (passthrough , store) ∷ []   -- FUEL EXHAUSTED
solveWorklist c (suc f) []       passthrough store = (passthrough , store) ∷ []
solveWorklist c (suc f) (op ∷ ws) passthrough store =
  concatMap
    (λ { (newOps , newPass , newStore) →
         solveWorklist c f (newOps ++ ws) (newPass ++ passthrough) newStore })
    (step c op store)

----------------------------------------------------------------------
----------------------------------------------------------------------
-- Partition a "normalized" constraint list into:
--   - a trusted Store (for entries that are clearly in canonical form)
--   - a list of "dirty" ops that must be re-solved via step
--     (because another solver may have polluted them, e.g. substituted
--      a compound term onto what used to be a variable side)
--
-- An entry is trusted iff:
--   - it's (var =ℒ term) with the variable not already claimed in the
--     store we're building, OR
--   - it's (term =ℒ var) symmetric form (we flip it), OR
--   - it's (var ≠ℒ nonvar) prohibited-value form, OR
--   - it's (var ≠ℒ var) suspended-dif form
--
-- Anything else (compound =ℒ compound, compound =ℒ compound ≠, or
-- a var that would shadow an existing store entry) goes into the
-- dirty list to be re-solved.
----------------------------------------------------------------------

rebuildStore :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → List ((ℒ ∘ Code) c)
  → Store Code c × List ((ℒ ∘ Code) c)
rebuildStore {𝒞}{Code}{Constraint} c ops = go ops emptyStore []
  where
    eqv = λ x y → eqCode {c = 𝒞} {Code = Code} {witness = c} x y

    addProhibitedFast : ℕ → Code c → Store Code c → Store Code c
    addProhibitedFast n t st with Map.lookup st n
    ... | just (bound _)    = st
    ... | just (attr ps ss) = Map.insert n (attr (consUniq eqv t ps) ss) st
    ... | nothing           = Map.insert n (attr (t ∷ []) []) st

    -- A normalized entry is considered trusted iff the left side is
    -- still a variable. Pollution from other solvers can only replace
    -- a variable on the left with a concrete value; such entries go
    -- into the dirty list and are re-processed by `solveWorklist`.
    go : List ((ℒ ∘ Code) c)
       → Store Code c
       → List ((ℒ ∘ Code) c)
       → Store Code c × List ((ℒ ∘ Code) c)
    go []            st dirty = st , dirty
    go (op ∷ rest)   st dirty with op
    ... | l =ℒ r with varName l
    ...   | just n  = go rest (Map.insert n (bound r) st) dirty
    ...   | nothing = go rest st (op ∷ dirty)
    go (op ∷ rest) st dirty | l ≠ℒ r with varName l | varName r
    ...   | just n  | just m  = go rest (suspendDif n m st) dirty
    ...   | just n  | nothing = go rest (addProhibitedFast n r st) dirty
    ...   | nothing | just m  = go rest (addProhibitedFast m l st) dirty
    ...   | nothing | nothing = go rest st (op ∷ dirty)

----------------------------------------------------------------------
-- Serialize a store back to a normalized ℒ-list.
-- - bound entries become (var n =ℒ t)
-- - attributed entries become (var n ≠ℒ p) for each prohibited p,
--   and (var n ≠ℒ var m) for each suspended partner m > n
--   (the m>n filter dedupes the symmetric suspension pairs)
----------------------------------------------------------------------

serializeStore :
    ∀ {𝒞 : Set} {Code : 𝒞 → Set} {Constraint : 𝒞 → Set} (c : 𝒞)
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ vu : ValueUtils 𝒞 Code Constraint ⦄
  → Store Code c
  → List ((ℒ ∘ Code) c)
serializeStore {𝒞} {Code} {Constraint} c ⦃ _ ⦄ ⦃ _ ⦄ ⦃ vu ⦄ store =
  concatMap entryToOps (Map.toList store)
  where
    -- Deep-resolve a term: top-level walk, then substitute every
    -- store binding into the result (idempotent, order-independent).
    -- This ensures emitted terms like cons (var 5) (var 6) become
    -- cons a (var 6) when var 5 ↦ a is in the store, so downstream
    -- consumers don't see dangling variable references.
    deepResolve : Code c → Code c
    deepResolve t =
      let walked = walk store t in
      foldr (λ { (n , bound s) acc →
                   ValueUtils.apply vu c c n (walk store s) acc
               ; (_ , attr _ _) acc → acc })
            walked (Map.toList store)

    entryToOps : ℕ × Binding Code c → List ((ℒ ∘ Code) c)
    entryToOps (n , bound t)     = (fresh n =ℒ deepResolve t) ∷ []
    entryToOps (n , attr ps ss)  =
      Data.List.map (λ p → fresh n ≠ℒ deepResolve p) ps
      ++ Data.List.map (λ m → fresh n ≠ℒ fresh m)
           (filterᵇ (λ m → n <ᵇ m) ss)

----------------------------------------------------------------------
-- Public entrypoint. Matches the shape of the old unifyDisunify, but
-- takes TWO input lists: `normalized` (already-solved, trusted) and
-- `new` (to be processed this call).
--
-- Note: this solver never applies bindings to `other` (the user's A
-- parameter). Deferred substitution is handled once at the end by
-- the grounder, which is the same design principle that makes the
-- per-call path cheap.
----------------------------------------------------------------------

unifyDisunify :
    ∀ {𝒞 Code Constraint}
    {A : Set}
  → (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (occurs : ℕ → A → Bool)
  → (apply  : ℕ → Code c → A → A)
  → List ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)   -- normalized (prev result)
  → List ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)   -- new constraints this call
  → A
  → List ( List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
               ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
         × A )
unifyDisunify {𝒞}{Code}{Constraint}{A} c oc ap normalized new other =
  let
    -- Strip the Dual-⊥ side; it's impossible so it's always inj₁.
    stripSum : List ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)
             → List ((ℒ ∘ Code) c)
    stripSum = catMaybes ∘ Data.List.map
                 (λ { (inj₁ x) → just x ; (inj₂ _) → nothing })

    normOps = stripSum normalized
    newOps  = stripSum new

    -- 1. Rebuild the store from the normalized list, partitioning
    --    it into trusted bindings and dirty ops that must be re-solved.
    --    An entry is dirty iff its left side is no longer a variable
    --    (pollution: another solver substituted a concrete value into
    --    what used to be a variable binding).
    rebuilt     = rebuildStore c normOps
    initialStore = proj₁ rebuilt
    dirtyOps     = proj₂ rebuilt

    -- 2. Solve all ops (dirty + new) against the partial store.
    branches = solveWorklist c 10000 (dirtyOps ++ newOps) [] initialStore
  in
  -- 3. For each successful branch, serialize the store back out
  --    (wrapping into Σᵢ via _:-:_) and apply bindings to `other`.
  --    Re-applying old bindings is safe because pollution preserves
  --    semantics — a variable that was already replaced in `other`
  --    will simply be a no-op on re-application.
  Data.List.map
    (λ { (passthrough , finalStore) →
       let serialized = serializeStore c finalStore
           wrapped    = Data.List.map
                          (λ l → inj₁ (_:-:_ c l))
                          serialized
       in (wrapped ++ passthrough , other)
    })
    branches

----------------------------------------------------------------------
-- Grounder.
--
-- Run once at the end of a derivation. Takes the accumulated
-- constraint store (possibly chained — e.g. var 1 ↦ var 10 ↦ cons)
-- and produces a fully-resolved view: each variable mapped to the
-- deepest term the store knows about, with all substitutions applied.
--
-- Implementation: rebuild the union-find store from the input list,
-- then for every bound entry emit (n , deeply-resolved term). For
-- every prohibited value emit (n , deeply-resolved prohibited term)
-- on the disequality side. Suspended var-var difs are emitted as a
-- pair of variable ids on the disequality side (since neither side
-- is a ground term yet).
--
-- Cross-solver (Dual ∘ Constraint) entries are ignored — this
-- grounder only resolves unification-style bindings for its own
-- solver. The caller is expected to ground other solvers separately.
--
-- The `other` value is threaded through and all store bindings
-- applied to it (using ValueUtils.apply which walks deeply). This
-- is the "MGU is ready" step that used to happen per-call; now it
-- happens exactly once.
----------------------------------------------------------------------

groundImpl :
    ∀ {A : Set} {𝒞 : Set} {Code : 𝒞 → Set} {Constraint : 𝒞 → Set}
  → (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ vu : ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (occurs : ℕ → A → Bool)
  → (apply  : ℕ → Code c → A → A)
  → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
  → A
  → List ((ℕ × Code c) ⊎ (ℕ × Code c)) × A
groundImpl {A}{𝒞}{Code}{Constraint} c ⦃ dec ⦄ ⦃ ftu ⦄ ⦃ vu ⦄ oc ap input other =
  finalize branches
  where
    stripSum : List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
             → List ((ℒ ∘ Code) c)
    stripSum = catMaybes ∘ Data.List.map
                 (λ { (inj₁ x) → just x ; (inj₂ _) → nothing })

    ops : List ((ℒ ∘ Code) c)
    ops = stripSum input

    rebuilt : Store Code c × List ((ℒ ∘ Code) c)
    rebuilt = rebuildStore c ops

    initialStore : Store Code c
    initialStore = proj₁ rebuilt

    dirtyOps : List ((ℒ ∘ Code) c)
    dirtyOps = proj₂ rebuilt

    branches : List ( List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
                          ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
                    × Store Code c )
    branches = solveWorklist c 10000 dirtyOps [] initialStore

    -- Deep-resolve a term against a given store, using apply across
    -- the whole store (which recurses into compounds).
    deepResolve : Store Code c → Code c → Code c
    deepResolve st t =
      foldr (λ { (n , bound s) acc →
                   ValueUtils.apply vu c c n (walk st s) acc
               ; (_ , attr _ _) acc → acc })
            (walk st t) (Map.toList st)

    entryToResult : Store Code c
                  → ℕ × Binding Code c
                  → List ((ℕ × Code c) ⊎ (ℕ × Code c))
    entryToResult st (n , bound t)     =
      inj₁ (n , deepResolve st t) ∷ []
    entryToResult st (n , attr ps ss)  =
      Data.List.map (λ p → inj₂ (n , deepResolve st p)) ps
      ++ Data.List.map (λ m → inj₂ (n , walk st (fresh m)))
           (filterᵇ (λ m → n <ᵇ m) ss)

    applyStoreDeep : Store Code c → A → A
    applyStoreDeep st acc0 =
      foldr (λ { (n , bound t) acc →
                   ap n (deepResolve st t) acc
               ; (_ , attr _ _) acc → acc })
            acc0 (Map.toList st)

    finalize : List ( List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
                          ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
                    × Store Code c )
             → List ((ℕ × Code c) ⊎ (ℕ × Code c)) × A
    finalize []                      = [] , other
    finalize ((_ , finalStore) ∷ _)  =
      concatMap (entryToResult finalStore) (Map.toList finalStore)
      , applyStoreDeep finalStore other