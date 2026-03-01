module Term.nqueens where

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

data BoolLogic : Set where
  true : BoolLogic
  false : BoolLogic
  varBool : ℕ → BoolLogic

boolD : HasDesc BoolLogic
boolD = deriveDesc BoolLogic

natD : HasDesc ℕ
natD = deriveDesc ℕ

data ℕLogic : Set where
  zero : ℕLogic
  suc : ℕLogic → ℕLogic
  varℕ : ℕ → ℕLogic

data FD : Set where
  zero  : FD
  suc   : FD → FD
  varFD : ℕ → FD

  _#+_   : FD → FD → FD
  _-_   : FD → FD → FD
  abs   : FD → FD

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

data ℒℕ : Set where
  _<ℒℕ_ : ℕLogic → ℕLogic → ℒℕ

data ℒFD : Set where
  _<FD_   : FD → FD → ℒFD
  _≤FD_   : FD → FD → ℒFD
  _>FD_   : FD → FD → ℒFD
  _≥FD_   : FD → FD → ℒFD
  _inFD_  : FD → FD → FD → ℒFD

data ℒList (A : Set) : Set where
  _<ℒList_ : ListLogic A → ListLogic A → ℒList A

pattern _<ℕ_ x y = (default (x <ℒℕ y))
pattern _<List_ x y = (default (x <ℒList y))

pattern _≥ℕ_ x y = (dual (x <ℒℕ y))
pattern _≥List_ x y = (dual (x <ℒList y))

infix 200 _<ℒℕ_
infix 200 _<ℒList_

data Index : Set where
  BoolI  : Index
  NatI  : Index
  FDI    : Index
  ×I : (i : Index) → Index
  ListI : (i : Index) → Index

⟦_⟧ : Index → Set
⟦ BoolI ⟧    = BoolLogic
⟦ NatI ⟧    = ℕLogic
⟦ FDI ⟧    = FD
⟦ ×I i ⟧    = ×Logic ⟦ i ⟧
⟦ ListI i ⟧ = ListLogic ⟦ i ⟧

⟦_⟧ℒ : Index → Set
⟦ BoolI ⟧ℒ    = ⊤
⟦ NatI ⟧ℒ    = ℒℕ
⟦ FDI ⟧ℒ   = ℒFD
⟦ ×I i ⟧ℒ    = ⊤
⟦ ListI i ⟧ℒ = ℒList ⟦ i ⟧

natLD : HasDesc ℕLogic
natLD = deriveDesc ℕLogic

fdD : HasDesc FD
fdD = deriveDesc FD

×D : HasDesc ×Logic
×D = deriveDesc ×Logic

listD : HasDesc ListLogic
listD = deriveDesc ListLogic

natLCD : HasDesc ℒℕ
natLCD = deriveDesc ℒℕ

fdLCD : HasDesc ℒFD
fdLCD = deriveDesc ℒFD

listLCD : HasDesc ℒList
listLCD = deriveDesc ℒList

data Functor (A : Set) : Set where
  not    : Functor A → Functor A

  nQueens : FD → ListLogic FD → Functor A
  lengthF : ListLogic A → FD → Functor A
  ins     : ListLogic FD → FD → FD → Functor A
  safeQ1  : ListLogic FD → Functor A
  safeQ3  : ListLogic FD → FD → FD → Functor A

  true   : Functor A
  false  : Functor A

validate : ∀ {A} → Where → AbstractOrConcrete → Functor A → Set
validate _ abstr (not _) = ⊤
validate bodyOfRule concr (not _) = ⊤
validate bodyOfRule _ true = ⊤
validate _ _ false = ⊤
validate _ _ _ = ⊤

functorD : HasDesc Functor
functorD = deriveDesc Functor

indexD : HasDesc Index
indexD = deriveDesc Index

instance  decIndex : DecEq Index
          decIndex = deriveDecEq indexD

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

instance
  makeVarFD : MakeVar FD
  makeVarFD .fresh = varFD
  makeVarFD .new   = varFD 0

  unifyDisunifyFD : FTUtils FD
  unifyDisunifyFD = deriveFTUtils fdD

  ftUtilsFDCons : FTUtils ℒFD
  ftUtilsFDCons = deriveFTUtils fdLCD

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

zipValue : (i : Index) → ⟦ i ⟧ → ⟦ i ⟧ → Maybe (List (Σ Index (ℒ ∘ ⟦_⟧)))
zipValue (ListI _) [] [] = just []
zipValue (ListI i) (x ∷ xs) (y ∷ ys) = just ((i , x =ℒ y) ∷ (ListI i , xs =ℒ ys) ∷ [])
zipValue _ _ _ = nothing

zipAtom : (i : Index) → Functor ⟦ i ⟧ → Functor ⟦ i ⟧ → Maybe (List (Σ Index (ℒ ∘ ⟦_⟧)))
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

instance  solver : Solver Index ⟦_⟧ ⟦_⟧ℒ
          solver .solve (ListI NatI) = concreteListNatSolver
          solver .solve (ListI x) = abstractListSolver x
          solver .solve = unifyDisunify

instance  scheduler : Scheduler Index ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ decIndex ⦄ ⦃ solver ⦄

module program where
  open Term.types

  lengthProgram :
    Clause (Functor FD) validate Index ⟦_⟧ ⟦_⟧ℒ
  lengthProgram = do

    lengthF [] zero •

    Q   ← new
    Qs  ← new
    N   ← new
    N1  ← new

    lengthF (Q ∷ Qs) N :-
        (□ (FDI :-: (N =ℒ (N1 #+ suc zero))))
      ↼  lengthF Qs N1 •

  insProgram :
    Clause (Functor FD) validate Index ⟦_⟧ ⟦_⟧ℒ
  insProgram = do

    L ← new
    H ← new

    ins [] L H •

    Q  ← new
    Qs ← new
    L′ ← new
    H′ ← new

    ins (Q ∷ Qs) L′ H′ :-
        (◇ (FDI :-: (Q ≥FD L′)))
      ↼  (◇ (FDI :-: (Q ≤FD H′)))
      ↼  ins Qs L′ H′ •

  nQueensProgram :
    Clause (Functor FD) validate Index ⟦_⟧ ⟦_⟧ℒ
  nQueensProgram = do

    N  ← new
    Qs ← new

    nQueens N Qs :-
        lengthF Qs N
      ∧  ins Qs (suc zero) N
      ∧  safeQ1 Qs •

    safeQ1 [] •

    Q  ← new
    Qs ← new

    safeQ1 (Q ∷ Qs) :-
        safeQ3 Qs Q (suc zero)
      ∧  safeQ1 Qs •

    Q0 ← new
    D0 ← new

    safeQ3 [] Q0 D0 •

    Q   ← new
    Qs  ← new
    Q0′ ← new
    D0′ ← new
    D1  ← new

    safeQ3 (Q ∷ Qs) Q0′ D0′ :-
        (□ (FDI :-: (Q0′ ≠ℒ Q)))                          -- #\=
      ↼  (□ (FDI :-: (abs (Q0′ - Q) ≠ℒ D0′)))              -- diagonal
      ↼  (□ (FDI :-: (D1 =ℒ (D0′ #+ suc zero))))            -- D1 #=
      ↼  safeQ3 Qs Q0′ D1 •
  
  groundProgram = applyVars nQueensProgram 0

  question :
    Body (Functor ℕLogic) (validate bodyOfRule) Index ⟦_⟧ ⟦_⟧ℒ
  question = 
    nQueens 8 (varList 0) •

  execute = eval (zipAtom NatI) zipValue (toIntern groundProgram) (toLiteralList question) [] false []