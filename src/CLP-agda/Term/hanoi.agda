module Term.hanoi where

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

data ℒList (A : Set) : Set where
  _<ℒList_ : ListLogic A → ListLogic A → ℒList A

data NoConstraint : Set where

pattern _<ℕ_ x y = (default (x <ℒℕ y))
pattern _<List_ x y = (default (x <ℒList y))

pattern _≥ℕ_ x y = (dual (x <ℒℕ y))
pattern _≥List_ x y = (dual (x <ℒList y))

infix 200 _<ℒℕ_
infix 200 _<ℒList_

data Index : Set where
  BoolI  : Index
  NatI  : Index
  ×I : (i : Index) → Index
  ListI : (i : Index) → Index

⟦_⟧ : Index → Set
⟦ BoolI ⟧    = BoolLogic
⟦ NatI ⟧    = ℕLogic
⟦ ×I i ⟧    = ×Logic ⟦ i ⟧
⟦ ListI i ⟧ = ListLogic ⟦ i ⟧

⟦_⟧ℒ : Index → Set
⟦ BoolI ⟧ℒ    = NoConstraint
⟦ NatI ⟧ℒ    = ℒℕ
⟦ ×I i ⟧ℒ    = NoConstraint
⟦ ListI i ⟧ℒ = ℒList ⟦ i ⟧

natLD : HasDesc ℕLogic
natLD = deriveDesc ℕLogic

×D : HasDesc ×Logic
×D = deriveDesc ×Logic

listD : HasDesc ListLogic
listD = deriveDesc ListLogic

natLCD : HasDesc ℒℕ
natLCD = deriveDesc ℒℕ

listLCD : HasDesc ℒList
listLCD = deriveDesc ℒList

restLCD : HasDesc NoConstraint
restLCD = deriveDesc NoConstraint

data Functor (A : Set) : Set where
  fnot    : Functor A → Functor A
  dupli  : ListLogic A → ListLogic (×Logic A) → Functor A
  append : ListLogic (×Logic A) → ListLogic (×Logic A) → ListLogic (×Logic A) → Functor A
  hanoi  : ℕLogic → A → A → A → ListLogic (×Logic A) → Functor A
  hanoiMoves : ℕLogic → ListLogic (×Logic A) → Functor A
  ftrue   : Functor A
  ffalse  : Functor A

validate : ∀ {A} → Where → AbstractOrConcrete → Functor A → Set
validate _ abstr (fnot _) = ⊤
validate bodyOfRule concr (fnot _) = ⊤
validate _ _ (dupli _ _) = ⊤
validate bodyOfRule _ ftrue = ⊤
validate _ _ ffalse = ⊤
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

instance  ftUtilsRestCns : FTUtils NoConstraint
          ftUtilsRestCns = deriveFTUtils restLCD

instance  ftUtilsListCns : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ℒList A)
          ftUtilsListCns = deriveFTUtils listLCD

applyFunctor : (i₀ : Index) → (i₁ : Index) → ℕ → ⟦ i₀ ⟧ → ⟦ i₁ ⟧ → ⟦ i₁ ⟧
applyFunctor BoolI BoolI n subst (varBool m) = if m ≡ᵇ n then subst else (varBool m)
applyFunctor i₀ BoolI n subst (varBool m) = varBool m
applyFunctor i₀ BoolI n subst expr = expr
applyFunctor NatI NatI n subst (varℕ m) = if m ≡ᵇ n then subst else (varℕ m)
applyFunctor i₀ NatI n subst (varℕ m) = varℕ m
applyFunctor i₀ NatI n subst zero = zero
applyFunctor i₀ NatI n subst (suc x) = applyFunctor i₀ NatI n subst x
applyFunctor (ListI i₀) (ListI i₁) n subst (varList m) with i₀ ≟ i₁
... | yes refl =  if m ≡ᵇ n then subst else (varList m)
... | no _ = varList m
applyFunctor i₀ (ListI i₁) n subst (varList m) = varList m
applyFunctor i₀ (ListI i₁) n subst [] = []
applyFunctor i₀ (ListI i₁) n subst (x ∷ xs) = applyFunctor i₀ i₁ n subst x ∷ applyFunctor i₀ (ListI i₁) n subst xs
applyFunctor (×I i₀) (×I i₁) n subst (var× m) with i₀ ≟ i₁
... | yes refl =  if m ≡ᵇ n then subst else (var× m)
... | no _ = var× m
applyFunctor i₀ (×I i₁) n subst (var× m) = var× m
applyFunctor i₀ (×I i₁) n subst (x ∶ y) = applyFunctor i₀ i₁ n subst x ∶ applyFunctor i₀ i₁ n subst y

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

zipValue : (i : Index) → ⟦ i ⟧ → ⟦ i ⟧ → Maybe (List (Σᵢ Index (ℒ ∘ ⟦_⟧) ⟦_⟧ ⟦_⟧ℒ))
zipValue BoolI true true = just []
zipValue BoolI false false = just []
zipValue NatI zero zero = just []
zipValue NatI (suc x) (suc y) = just ((_:-:_ NatI (x =ℒ y)) ∷ [])
zipValue (ListI _) [] [] = just []
zipValue (ListI i) (x ∷ xs) (y ∷ ys) = 
  just ((_:-:_ i (x =ℒ y) ⦃ mapType i ⦄ ⦃ mapConstraint i ⦄) ∷ (_:-:_ (ListI i) (xs =ℒ ys) ⦃ mapType (ListI i) ⦄ ⦃ mapConstraint (ListI i) ⦄) ∷ [])
zipValue (×I i) (x ∶ y) (a ∶ b) = 
  just ((_:-:_ i (x =ℒ a) ⦃ mapType i ⦄ ⦃ mapConstraint i ⦄) ∷ (_:-:_ i (y =ℒ b) ⦃ mapType i ⦄ ⦃ mapConstraint i ⦄) ∷ [])
zipValue _ _ _ = nothing

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

  appendProgram :
    (i : Index) →
    ⦃ FTUtils ⟦ i ⟧ ⦄ →
    ⦃ MakeVar ⟦ i ⟧ ⦄ →
    Clause (Functor ⟦ i ⟧) validate Index ⟦_⟧ ⟦_⟧ℒ
  appendProgram i = do

    L ← new

    append [] L L •

    H  ← new
    T  ← new
    L2 ← new
    R  ← new

    append (H ∷ T) L2 (H ∷ R) :-
        append T L2 R •

  hanoiProgram :
    Clause (Functor ℕLogic) validate Index ⟦_⟧ ⟦_⟧ℒ
  hanoiProgram = do
    appendProgram NatI

    A ← new
    B ← new
    X ← new

    hanoi (suc zero) A B X ((A ∶ B) ∷ []) •

    N      ← new
    A₁     ← new
    B₁     ← new
    C₁     ← new
    Moves  ← new
    Moves1 ← new
    Moves2 ← new

    hanoi (suc N) A₁ B₁ C₁ Moves :-
        hanoi N A₁ C₁ B₁ Moves1
      ∧  hanoi N C₁ B₁ A₁ Moves2
      ∧  append Moves1 ((A₁ ∶ B₁) ∷ Moves2) Moves •

    let a = zero
    let b = suc zero
    let c = suc (suc zero)

    N₂     ← new
    Moves₀ ← new

    hanoiMoves N₂ Moves₀ :-
        hanoi N₂ a b c Moves₀ •

  groundProgram = applyVars hanoiProgram 0

  question :
    Body (Functor ℕLogic) (validate bodyOfRule) Index ⟦_⟧ ⟦_⟧ℒ
  question = 
    hanoiMoves (suc (suc (suc zero))) (varList 0) •

  execute = eval (zipAtom NatI) zipValue ((toIntern ∘ proj₂) groundProgram) (toLiteralList question) [] false