module Term.streamreasoning where

open import Data.Bool hiding (_≟_ ; _∧_)
open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Function.Base

open import Generics

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Term.ftUtilsDerivation
open import Term.types
open import Term.unifyDisunify
open import Term.solverScheduler
open import Term.clp
open import FD.domain

⟦_⟧ : Index → Set
⟦ BoolI ⟧    = BoolLogic
⟦ FDI ⟧    = ℕLogic
⟦ ×I i ⟧    = ×Logic ⟦ i ⟧

⟦_⟧ℒ : Index → Set
⟦ BoolI ⟧ℒ    = ⊤
⟦ NatI ⟧ℒ    = ℒℕ
⟦ ×I i ⟧ℒ    = ⊤

data Functor : Set where
  fnot    : Functor → Functor
  validStream : FD → PQ → Functor
  stream : FD → PQ → Functor
  cancelled : FD → PQ → Functor
  higherPrio : FD → FD → Functor
  incompt : PQ → PQ → Functor
  ffalse  : Functor

isNot : Functor → Bool
isNot (fnot _) = true
isNot _ = false

isForall : Functor → Bool
isForall (fforall _ _ _) = true
isForall _ = false

validate : ∀ {A} → Where → AbstractOrConcrete → Functor A → Set
validate _ abstr (fnot _) = ⊤
validate bodyOfRule concr (fnot _) = ⊤
validate _ _ (dupli _ _) = ⊤
validate bodyOfRule _ ftrue = ⊤
validate _ _ ffalse = ⊤
validate _ _ _ = ⊤

indexD : HasDesc Index
indexD = deriveDesc Index

instance  decIndex : DecEq Index
          decIndex = deriveDecEq indexD

incrementFunctor : (i : Index) → ℕ → ⟦ i ⟧ → ⟦ i ⟧
incrementFunctor BoolI n (varBool m) = varBool (m + n)
incrementFunctor BoolI n expr = expr
incrementFunctor NatI n (varℕ m) = varℕ (m + n)
incrementFunctor NatI n zero = zero
incrementFunctor NatI n (suc x) = incrementFunctor NatI n x
incrementFunctor (ListI i) n (varList m) = varList (m + n)
incrementFunctor (ListI i) n [] = []
incrementFunctor (ListI i) n (x ∷ xs) = incrementFunctor i n x ∷ incrementFunctor (ListI i) n xs
incrementFunctor (×I i) n (var× m) = var× (m + n)
incrementFunctor (×I i) n (x ∶ y) = incrementFunctor i n x ∶ incrementFunctor i n y

mapType : (i : Index) → FTUtils ⟦ i ⟧
mapType BoolI      = unifyDisunifyBool
mapType NatI       = unifyDisunifyNatL
mapType (×I i)     = unifyDisunify×  ⦃ mapType i ⦄
mapType (ListI i)  = unifyDisunifyList ⦃ mapType i ⦄

mapConstraint : (i : Index) → FTUtils ⟦ i ⟧ℒ
mapConstraint BoolI      = ftUtilsRestCns
mapConstraint NatI       = ftUtilsNatCns
mapConstraint (×I i)     = ftUtilsRestCns
mapConstraint (ListI i)  = ftUtilsListCns ⦃ mapType i ⦄

zipAtom : (i : Index) → Functor ⟦ i ⟧ → Functor ⟦ i ⟧ → Maybe (List (Σᵢ Index (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ))
zipAtom i (dupli x y) (dupli a b) = 
  just ((_:-:_ (ListI i) (x =ℒ a) ⦃ mapType (ListI i) ⦄ ⦃ mapConstraint (ListI i) ⦄) ∷ (_:-:_ (ListI (×I i)) (y =ℒ b) ⦃ mapType (ListI (×I i)) ⦄ ⦃ mapConstraint (ListI (×I i)) ⦄) ∷ [])
zipAtom i _ _ = nothing

instance  solver : Solver Index ⟦_⟧ ⟦_⟧ℒ
          solver .solve = unifyDisunify

instance  scheduler : Scheduler Index ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ decIndex ⦄ ⦃ solver ⦄

module program where
  open Term.types

  streamReasoning :
    Clause Functor validate Index ⟦_⟧ ⟦_⟧ℒ
  streamReasoning = do
    P ← new
    Data ← new

    validStream P Data :-
        stream P Data
      ∧  not (cancelled P Data) •
    
    P1 ← new

    cancelled P Data :-
        higherPrio P1 P
      ∧  stream P1 Data
      ∧  incompt Data Data1 •
    
    PHi ← new
    PLo ← new

    higherPrio PHi PLo :-
        PHi ＃> PLo •
    
    X ← new

    incompt (inj₁ X) (inj₂ X) •
    incompt (inj₂ X) (inj₁ X) •

    stream zero (inj₁ X) •
    stream (suc zero) (inj₁ true) •
    stream (suc (suc zero)) (inj₁ false) •
    stream (suc (suc (suc zero))) (inj₁ true) •

  groundProgram = applyVars hanoiProgram 0

  question :
    Body (Functor ℕLogic) (validate bodyOfRule) Index ⟦_⟧ ⟦_⟧ℒ
  question = 
    hanoiMoves (suc (suc (suc zero))) (varList 0) •

  execute = eval (zipAtom NatI) zipValue ((toIntern ∘ proj₂) groundProgram) (toLiteralList question) [] false