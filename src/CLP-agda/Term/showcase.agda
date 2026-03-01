module Term.showcase where

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

open import Agda.Builtin.Reflection hiding (Clause)
open import Term.domainUniverseGeneration hiding (_>>=_; _>>_)

open import Term.ftUtilsDerivation
open import Term.types
open import Term.unifyDisunify
open import Term.solverScheduler

-- Domain Types

data BoolLogic : Set where
  true : BoolLogic
  false : BoolLogic
  varBool : ℕ → BoolLogic

data ℕLogic : Set where
  zero : ℕLogic
  suc : ℕLogic → ℕLogic
  varℕ : ℕ → ℕLogic

module LogicTypes where

  data ×Logic (A : Set) : Set where
    _∶_ : A → A → ×Logic A
    var× : ℕ → ×Logic A

  data ListLogic (A : Set) : Set where
    []  : ListLogic A
    _∷_ : A → ListLogic A → ListLogic A
    varList : ℕ → ListLogic A

open LogicTypes

infixl 21 _∶_
infixr 20 _∷_

-- Constraint Types

data ℒℕ : Set where
  _<ℒℕ_ : ℕLogic → ℕLogic → ℒℕ

data ℒList (A : Set) : Set where
  _<ℒList_ : ListLogic A → ListLogic A → ℒList A

pattern _<ℕ_ x y = (default (x <ℒℕ y))
pattern _<List_ x y = (default (x <ℒList y))

pattern _≥ℕ_ x y = (dual (x <ℒℕ y))
pattern _≥List_ x y = (dual (x <ℒList y))

infix 200 _<ℒℕ_
infix 200 _<ℒList_

-- Atom Type

data Functor (A : Set) : Set where
  not : Functor A → Functor A
  dupli : ListLogic A → ListLogic (×Logic A) → Functor A
  fforall : (i : Index) → ⟦ i ⟧ → Functor → Functor
  true : Functor A
  false : Functor A

-- Universe

-- list of names you want in the universe
myTypes : List Name
myTypes = quote BoolLogic ∷ quote ℕLogic ∷ quote ×Logic ∷ quote ListLogic ∷ []

-- the top-level declaration
-- unquoteDecl data My𝒞 constructor Bool𝒞 Nat𝒞 ×𝒞 List𝒞 = makeUniverse myTypes

data My𝒞 : Set where
  Bool𝒞  : My𝒞
  Nat𝒞  : My𝒞
  ×𝒞 : (i : My𝒞) → My𝒞
  List𝒞 : (i : My𝒞) → My𝒞
{-
newConstraintDomainSystem (withAtom Functor)
 ((Nat withConstraints (_<N_ and _<=N_ and empty)) and
 (List withConstraints (_<List_ and _<=List_ and empty)) and
 (_×_ withConstraints empty) and
 empty)
-}
⟦_⟧ : My𝒞 → Set
⟦ Bool𝒞 ⟧    = BoolLogic
⟦ Nat𝒞 ⟧    = ℕLogic
⟦ ×𝒞 i ⟧    = ×Logic ⟦ i ⟧
⟦ List𝒞 i ⟧ = ListLogic ⟦ i ⟧

⟦_⟧ℒ : My𝒞 → Set
⟦ Bool𝒞 ⟧ℒ    = ⊤
⟦ Nat𝒞 ⟧ℒ    = ℒℕ
⟦ ×𝒞 i ⟧ℒ    = ⊤
⟦ List𝒞 i ⟧ℒ = ℒList ⟦ i ⟧

-- Desc and Instances

natD : HasDesc ℕ
natD = deriveDesc ℕ

indexD : HasDesc My𝒞
indexD = deriveDesc My𝒞

instance  decMy𝒞 : DecEq My𝒞
          decMy𝒞 = deriveDecEq indexD

natLD : HasDesc ℕLogic
natLD = deriveDesc ℕLogic

boolD : HasDesc BoolLogic
boolD = deriveDesc BoolLogic

×D : HasDesc ×Logic
×D = deriveDesc ×Logic

listD : HasDesc ListLogic
listD = deriveDesc ListLogic

natLCD : HasDesc ℒℕ
natLCD = deriveDesc ℒℕ

listLCD : HasDesc ℒList
listLCD = deriveDesc ℒList

functorD : HasDesc Functor
functorD = deriveDesc Functor

instance  makeVarBool : MakeVar BoolLogic
          makeVarBool .fresh = varBool
          makeVarBool .new = varBool 0

instance  makeVarℕ : MakeVar ℕLogic
          makeVarℕ .fresh = varℕ
          makeVarℕ .new = varℕ 0

instance  makeVarList : ∀ {A} → MakeVar (ListLogic A)
          makeVarList .fresh = varList
          makeVarList .new = varList 0

instance  makeVar× : ∀ {A} → MakeVar (×Logic A)
          makeVar× .fresh = var×
          makeVar× .new = var× 0

instance  unifyDisunifyNat : FTUtils ℕ
          unifyDisunifyNat = deriveFTUtils natD

instance  unifyDisunifyBool : FTUtils BoolLogic
          unifyDisunifyBool = deriveFTUtils boolD

instance  unifyDisunifyNatL : FTUtils ℕLogic
          unifyDisunifyNatL = deriveFTUtils natLD

instance  unifyDisunifyList : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ListLogic A)
          unifyDisunifyList = deriveFTUtils listD

instance  unifyDisunify× : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (×Logic A)
          unifyDisunify× = deriveFTUtils ×D

instance  ftUtilsFunctor : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (Functor A)
          ftUtilsFunctor = deriveFTUtils functorD

instance  ftUtilsNatCns : FTUtils ℒℕ
          ftUtilsNatCns = deriveFTUtils natLCD

instance  ftUtilsListCns : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ℒList A)
          ftUtilsListCns = deriveFTUtils listLCD

zipValue : (i : My𝒞) → ⟦ i ⟧ → ⟦ i ⟧ → Maybe (List (Σ My𝒞 (ℒ ∘ ⟦_⟧)))
zipValue (List𝒞 _) [] [] = just []
zipValue (List𝒞 i) (x ∷ xs) (y ∷ ys) = just ((i , x =ℒ y) ∷ (List𝒞 i , xs =ℒ ys) ∷ [])
zipValue _ _ _ = nothing

zipAtom : (i : My𝒞) → Functor ⟦ i ⟧ → Functor ⟦ i ⟧ → Maybe (List (Σ My𝒞 (ℒ ∘ ⟦_⟧)))
zipAtom i (dupli x y) (dupli a b) = just ((List𝒞 i , x =ℒ a) ∷ (List𝒞 (×𝒞 i) , y =ℒ b) ∷ [])
zipAtom i _ _ = nothing

abstractListSolver : 
  ∀ {𝒞 Code Constraint}
  → (c : 𝒞) 
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → List ((ℒ ∘ ListLogic) (Code c) ⊎ (Dual ∘ ℒList) (Code c))
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
abstractListSolver c _ ((inj₁ x) ∷ xs) = {!   !}
abstractListSolver c _ ((inj₂ x) ∷ xs) = {!   !}
abstractListSolver c _ [] = {!   !}

concreteListNatSolver : 
  ∀ {𝒞 Code Constraint}
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → List ((ℒ ∘ ListLogic) ℕLogic ⊎ (Dual ∘ ℒList) ℕLogic)
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
concreteListNatSolver _ ((inj₁ x) ∷ xs) = {!   !}
concreteListNatSolver _ ((inj₂ x) ∷ xs) = {!   !}
concreteListNatSolver _ [] = {!   !}

instance  solver : Solver My𝒞 ⟦_⟧ ⟦_⟧ℒ
          solver .solve (List𝒞 Nat𝒞) = concreteListNatSolver
          solver .solve (List𝒞 x) = abstractListSolver x
          solver .solve = unifyDisunify

instance  scheduler : Scheduler My𝒞 ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ decMy𝒞 ⦄ ⦃ solver ⦄

validate : ∀ {A} → Where → AbstractOrConcrete → Functor A → Set
validate _ abstr (not _) = ⊤
validate bodyOfRule concr (not _) = ⊤
validate _ _ (dupli _ _) = ⊤
validate bodyOfRule _ true = ⊤
validate _ _ false = ⊤
validate _ _ _ = ⊥

module program where
  open Term.types

  -- ---------------------------------------------------------------------
  -- Example program
  dupliProgram : (i : My𝒞) → ⦃ FTUtils ⟦ i ⟧ ⦄ → ⦃ MakeVar ⟦ i ⟧ ⦄ → Clause (Functor ⟦ i ⟧) validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  dupliProgram i = do

    dupli [] [] •

    X ← new
    Xs ← new
    Ys ← new

    dupli (X ∷ Xs) (X ∶ X ∷ Ys) :-
      dupli Xs Ys ∧
      (◇ (List𝒞 i :-: (Xs ≥List Xs))) ↼•
      --◇ :-: Xs ≥List Xs ↼•
  -- ---------------------------------------------------------------------
  -- Example program
  dupliNatProgram : Clause (Functor ℕLogic) validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  dupliNatProgram = do
    dupliProgram Nat𝒞

  -- ---------------------------------------------------------------------
  -- Example program
  dupliBoolProgram : Clause (Functor BoolLogic) validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  dupliBoolProgram = do
    dupliProgram Bool𝒞

  test = applyVars (dupliProgram Nat𝒞) 0