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

decToBool : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

eqCode : ∀ {c : Set} {Code : c → Set} {witness : c}
       → ⦃ DecEq (Code witness) ⦄
       → Code witness → Code witness → Bool
eqCode x y = decToBool (x ≟ y)

memBy : {A : Set} → (A → A → Bool) → A → List A → Bool
memBy _  _ []       = false
memBy eq x (y ∷ ys) = if eq x y then true else memBy eq x ys

consUniq : {A : Set} → (A → A → Bool) → A → List A → List A
consUniq eq x xs = if memBy eq x xs then xs else x ∷ xs

unionBy : {A : Set} → (A → A → Bool) → List A → List A → List A
unionBy eq []       ys = ys
unionBy eq (x ∷ xs) ys =
  if memBy eq x ys then unionBy eq xs ys else x ∷ unionBy eq xs ys

-- A variable is either bound to a term or attributed with
-- prohibited values and suspended dif partner ids.
data Binding {𝒞 : Set} (Code : 𝒞 → Set) (c : 𝒞) : Set where
  bound : Code c → Binding Code c
  attr  : List (Code c) → List ℕ → Binding Code c

Store : ∀ {𝒞 : Set} → (Code : 𝒞 → Set) → 𝒞 → Set
Store Code c = Map (Binding Code c)

emptyStore : ∀ {𝒞 Code} {c : 𝒞} → Store Code c
emptyStore = Map.empty

-- Walk bound pointers; fuel = store size avoids non-termination on cycles
{-# TERMINATING #-}
walk₀ : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞}
      → ⦃ FTUtils (Code c) ⦄
      → ℕ → Store Code c → Code c → Code c
walk₀ zero    _     t = t
walk₀ (suc f) store t with varName t
... | nothing = t
... | just n  with Map.lookup store n
...   | just (bound t′) = walk₀ f store t′
...   | _               = t

walk : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞}
     → ⦃ FTUtils (Code c) ⦄
     → Store Code c → Code c → Code c
walk store t = walk₀ (suc (Map.size store)) store t

-- One step's result: a list of branches, each with new worklist items,
-- cross-solver passthrough constraints, and an updated store.
-- An empty list means failure.
StepResult :
    ∀ {𝒞 : Set} (Code Constraint : 𝒞 → Set) (c : 𝒞) → Set
StepResult {𝒞} Code Constraint c =
  List ( List ((ℒ ∘ Code) c)
       × List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
             ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
       × Store Code c )

-- Conservative check: can two terms possibly unify?
-- Variables always can; non-vars must match functor or have matching children.
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
          (just children) → allChildrenUnify children)
  where
    -- Cross-solver children are conservatively assumed to unify
    allChildrenUnify : List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) → Bool
    allChildrenUnify []       = true
    allChildrenUnify (ch ∷ chs) = allChildrenUnify chs

-- Return false if t could equal any prohibited value, true otherwise
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

-- Bind variable n to term t; check prohibited list and wake suspended difs
bindVar :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ℕ → Code c → Store Code c
  → Maybe (List ((ℒ ∘ Code) c) × Store Code c)
bindVar {𝒞}{Code}{Constraint} c ⦃ decc ⦄ ⦃ vu ⦄ ⦃ deccode ⦄ ⦃ mv ⦄ n t store
  with Map.lookup store n
... | just (bound _) = just ([] , store)
... | just (attr prohibited suspended) =
  if not (checkProhibited c t prohibited)
  then nothing
  else
    let store′  = Map.insert n (bound t) store
        wakeOps = Data.List.map (λ m → fresh n ≠ℒ fresh m) suspended
    in just (wakeOps , store′)
... | nothing =
  just ([] , Map.insert n (bound t) store)

-- Add t to the prohibited list of variable n; fail if n is already bound to t
addProhibited :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ℕ → Code c → Store Code c → Maybe (Store Code c)
addProhibited {𝒞}{Code}{Constraint} c n t store
  with Map.lookup store n
... | just (bound t′) =
  if canUnify c t′ t then nothing else just store
... | just (attr ps ss) =
  just (Map.insert n
         (attr (consUniq (λ x y → eqCode {c = 𝒞} {Code = Code} {witness = c} x y) t ps) ss)
         store)
... | nothing =
  just (Map.insert n (attr (t ∷ []) []) store)

-- Record a suspended dif(n, m) by linking both variable entries
addSuspended : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞} → ℕ → ℕ
             → Store Code c → Store Code c
addSuspended n m store with Map.lookup store n
... | just (bound _)     = store
... | just (attr ps ss)  =
  Map.insert n (attr ps (if any (λ k → k ≡ᵇ m) ss then ss else m ∷ ss)) store
... | nothing            = Map.insert n (attr [] (m ∷ [])) store

suspendDif : ∀ {𝒞 : Set} {Code : 𝒞 → Set} {c : 𝒞} → ℕ → ℕ → Store Code c → Store Code c
suspendDif n m store = addSuspended m n (addSuspended n m store)

-- Split zipMatch children into this-solver ops and cross-solver passthrough
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
  case getPermission c (inj₁ x) of λ where
    (just (inj₁ eq)) → (eq ∷ mine) , others
    _                → mine , (inj₁ x ∷ others)

-- Process one ℒ-operation against the store, returning all branches
step :
    ∀ {𝒞 Code Constraint} (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ vu : ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → (ℒ ∘ Code) c → Store Code c → StepResult Code Constraint c
step {𝒞}{Code}{Constraint} c ⦃ _ ⦄ ⦃ _ ⦄ ⦃ vu ⦄ op store with op
... | l =ℒ r =
  let l′ = walk store l
      r′ = walk store r
  in handleUnify l′ r′
  where
    handleUnify : Code c → Code c → StepResult Code Constraint c
    handleUnify a b with varName a | varName b
    -- both variables: merge, unioning attributes and waking suspensions
    ... | just n | just m =
      if n ≡ᵇ m
        then ([] , [] , store) ∷ []
        else
          (case (Map.lookup store n , Map.lookup store m) of λ where
            (just (attr pn sn) , just (attr pm sm)) →
              let eqv = λ x y → eqCode {c = 𝒞} {Code = Code} {witness = c} x y
                  mergedP = unionBy eqv pn pm
                  mergedS = unionBy (λ x y → x ≡ᵇ y)
                              (filterᵇ (λ k → not (k ≡ᵇ m)) sn)
                              (filterᵇ (λ k → not (k ≡ᵇ n)) sm)
                  store₁ = Map.insert n (attr mergedP mergedS) store
                  store₂ = Map.insert m (bound a) store₁
                  wakeOps = Data.List.map (λ k → fresh n ≠ℒ fresh k) mergedS
              in (wakeOps , [] , store₂) ∷ []
            (just (attr pn sn) , _) →
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
    -- left var: bind to right
    ... | just n | nothing =
      case bindVar c n b store of λ where
        nothing             → []
        (just (wake , st′)) → (wake , [] , st′) ∷ []
    -- right var: bind to left
    ... | nothing | just m =
      case bindVar c m a store of λ where
        nothing             → []
        (just (wake , st′)) → (wake , [] , st′) ∷ []
    -- both non-var: decompose via zipMatch
    ... | nothing | nothing =
      case ValueUtils.zipMatch vu c a b of λ where
        nothing         → []
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
    -- X ≠ X always fails
    ... | just n | just m =
      if n ≡ᵇ m
        then []
        else ([] , [] , suspendDif n m store) ∷ []
    -- var ≠ term: add to prohibited list
    ... | just n | nothing =
      case addProhibited c n b store of λ where
        nothing     → []
        (just st′)  → ([] , [] , st′) ∷ []
    ... | nothing | just m =
      case addProhibited c m a store of λ where
        nothing     → []
        (just st′)  → ([] , [] , st′) ∷ []
    -- both non-var: one branch per child, negating that child's equation
    ... | nothing | nothing =
      case ValueUtils.zipMatch vu c a b of λ where
        nothing →
          -- functor mismatch: deterministically succeeds
          ([] , [] , store) ∷ []
        (just children) →
          let mine , others = partitionChildren c children
          in makeBranches mine others
      where
        flipOp : (ℒ ∘ Code) c → (ℒ ∘ Code) c
        flipOp (x =ℒ y) = x ≠ℒ y
        flipOp (x ≠ℒ y) = x =ℒ y

        makeBranches :
            List ((ℒ ∘ Code) c)
          → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
                ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
          → StepResult Code Constraint c
        makeBranches []       _      = []
        makeBranches (x ∷ xs) others =
          (flipOp x ∷ [] , others , store)
          ∷ makeBranches xs others

-- Drain the worklist across all branches until empty or fuel exhausted
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
  → ℕ                                              -- fuel
  → List ((ℒ ∘ Code) c)                            -- worklist
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
        ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) -- accumulated passthrough
  → Store Code c
  → List ( List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
               ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
         × Store Code c )
solveWorklist c zero     _         passthrough store = (passthrough , store) ∷ []
solveWorklist c (suc f) []         passthrough store = (passthrough , store) ∷ []
solveWorklist c (suc f) (op ∷ ws) passthrough store =
  concatMap
    (λ { (newOps , newPass , newStore) →
         solveWorklist c f (newOps ++ ws) (newPass ++ passthrough) newStore })
    (step c op store)

-- Fast-path: load a normalized constraint list directly into the store.
-- Entries whose left side is no longer a variable are "dirty" and
-- returned for re-solving by solveWorklist.
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

    go : List ((ℒ ∘ Code) c) → Store Code c → List ((ℒ ∘ Code) c)
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

-- Serialize a store back to a normalized ℒ-list, deep-resolving all terms
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
    -- Walk then substitute all store bindings into a term
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

-- Entrypoint: solve new constraints against a previously-normalized store,
-- returning one (passthrough, updated-other) pair per surviving branch
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
    stripSum : List ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c) → List ((ℒ ∘ Code) c)
    stripSum = catMaybes ∘ Data.List.map
                 (λ { (inj₁ x) → just x ; (inj₂ _) → nothing })

    normOps = stripSum normalized
    newOps  = stripSum new

    -- Rebuild store from prior result; re-solve any dirty entries
    rebuilt      = rebuildStore c normOps
    initialStore = proj₁ rebuilt
    dirtyOps     = proj₂ rebuilt

    branches = solveWorklist c 10000 (dirtyOps ++ newOps) [] initialStore
  in
  Data.List.map
    (λ { (passthrough , finalStore) →
       let serialized = serializeStore c finalStore
           wrapped    = Data.List.map (λ l → inj₁ (_:-:_ c l)) serialized
       in (wrapped ++ passthrough , other)
    })
    branches

-- Extract ground bindings from a constraint list; apply them to other
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
    stripSum : List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c) → List ((ℒ ∘ Code) c)
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

    -- Walk then substitute all store bindings into a term
    deepResolve : Store Code c → Code c → Code c
    deepResolve st t =
      foldr (λ { (n , bound s) acc →
                   ValueUtils.apply vu c c n (walk st s) acc
               ; (_ , attr _ _) acc → acc })
            (walk st t) (Map.toList st)

    entryToResult : Store Code c → ℕ × Binding Code c
                  → List ((ℕ × Code c) ⊎ (ℕ × Code c))
    entryToResult st (n , bound t)    =
      inj₁ (n , deepResolve st t) ∷ []
    entryToResult st (n , attr ps ss) =
      Data.List.map (λ p → inj₂ (n , deepResolve st p)) ps
      ++ Data.List.map (λ m → inj₂ (n , walk st (fresh m)))
           (filterᵇ (λ m → n <ᵇ m) ss)

    applyStoreDeep : Store Code c → A → A
    applyStoreDeep st acc0 =
      foldr (λ { (n , bound t) acc → ap n (deepResolve st t) acc
               ; (_ , attr _ _) acc → acc })
            acc0 (Map.toList st)

    -- Use first branch only; take its bindings and apply them to other
    finalize : List ( List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
                          ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
                    × Store Code c )
             → List ((ℕ × Code c) ⊎ (ℕ × Code c)) × A
    finalize []                      = [] , other
    finalize ((_ , finalStore) ∷ _)  =
      concatMap (entryToResult finalStore) (Map.toList finalStore)
      , applyStoreDeep finalStore other