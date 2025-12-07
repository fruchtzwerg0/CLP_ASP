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

open import Term.ftUtilsDerivation
open import Term.types

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

pattern _<ℕ_ x y = (default (x <ℒℕ y))
pattern _<List_ x y = (default (x <ℒList y))

pattern _≥ℕ_ x y = (dual (x <ℒℕ y))
pattern _≥List_ x y = (dual (x <ℒList y))

infix 200 _<ℒℕ_
infix 200 _<ℒList_

data Index : Set where
  NatI  : Index
  ×I : (i : Index) → Index
  ListI : (i : Index) → Index

⟦_⟧ : Index → Set
⟦ NatI ⟧    = ℕLogic
⟦ ×I i ⟧    = ×Logic ⟦ i ⟧
⟦ ListI i ⟧ = ListLogic ⟦ i ⟧

⟦_⟧ℒ : Index → Set
⟦ NatI ⟧ℒ    = ℒℕ
⟦ ×I i ⟧ℒ    = ⊤
⟦ ListI i ⟧ℒ = ℒList ⟦ i ⟧

natLD : HasDesc ℕLogic
natLD = deriveDesc ℕLogic

×D : HasDesc ×Logic
×D = deriveDesc ×Logic

listD : HasDesc ListLogic
listD = deriveDesc ListLogic

data Functor (A : Set) : Set where
  not : Functor A → Functor A
  dupli : ListLogic A → ListLogic (×Logic A) → Functor A
  idC : A → A → Functor A
  true : Functor A
  false : Functor A

validate : ∀ {A} → Where → AbstractOrConcrete → Functor A → Set
validate _ abstr (not _) = ⊤
validate bodyOfRule concr (not _) = ⊤
validate _ _ (dupli _ _) = ⊤
validate bodyOfRule _ true = ⊤
validate _ _ false = ⊤
validate _ _ _ = ⊥

functorD : HasDesc Functor
functorD = deriveDesc Functor

indexD : HasDesc Index
indexD = deriveDesc Index

instance  decIndex : DecEq Index
          decIndex = deriveDecEq indexD

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

instance  unifyDisunifyNatL : FTUtils ℕLogic
          unifyDisunifyNatL = deriveFTUtils natLD

instance  unifyDisunifyList : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ListLogic A)
          unifyDisunifyList = deriveFTUtils listD

instance  unifyDisunify× : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (×Logic A)
          unifyDisunify× = deriveFTUtils ×D

instance  ftUtilsFunctor : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (Functor A)
          ftUtilsFunctor = deriveFTUtils functorD

getPermission' : (i : Index)
               → Σ Index (ℒ ∘ ⟦_⟧)
               → Maybe ((ℒ ∘ ⟦_⟧) i)
getPermission' x (_,_ b a ) with x ≟ b
... | no _ = nothing
... | (yes refl) = just a

getPermissionCustom' : (i : Index)
               → Σ Index (Dual ∘ ⟦_⟧ℒ)
               → Maybe ((Dual ∘ ⟦_⟧ℒ) i)
getPermissionCustom' x (_,_ b a ) with x ≟ b
... | no _ = nothing
... | (yes refl) = just a

instance  permission : Permission Index ⟦_⟧ ⟦_⟧ℒ
          permission .getPermission = getPermission'
          permission .getPermissionCustom = getPermissionCustom'

breakArgss : (i : Index) → ⟦ i ⟧ → ⟦ i ⟧ → Maybe (List (Σ Index (ℒ ∘ ⟦_⟧)))
breakArgss (ListI _) [] [] = just []
breakArgss (ListI i) (x ∷ xs) (y ∷ ys) = just ((i , x =ℒ y) ∷ (ListI i , xs =ℒ ys) ∷ [])
breakArgss _ _ _ = nothing
{-
breakArgsss : (i : Index) → Functor ⟦ i ⟧ → Functor ⟦ i ⟧ → Maybe (List (Σ Index (ℒ ∘ ⟦_⟧)))
breakArgsss i (dupli x y) (dupli a b) = just ((ListI i , x =ℒ a) ∷ (ListI (×I i) , y =ℒ b) ∷ [])

unifyDisunify : 
  {I B : Set}
  {Code : I → Set} 
  {Constraint : I → Set} 
  → ⦃ Permission I Code Constraint ⦄ 
  → (i : I) 
  → ⦃ FTUtils (Code i) ⦄ 
  → List ((Σ I (ℒ ∘ Code)) ⊎ B)
  → (Maybe ∘ List) (List ((Σ I (ℒ ∘ Code)) ⊎ B))
unifyDisunify witness ((inj₁ x) ∷ xs) with getPermission witness x
... | just (a =ℒ b) = {!   !}
... | just (a ≠ℒ b) = {!   !}
... | nothing = {!   !}
unifyDisunify witness y = {!   !}

chooseSolver :
  (i : Index)
  → List ((Σ Index (ℒ ∘ ⟦_⟧)) ⊎ (Σ Index (Dual ∘ ⟦_⟧ℒ))) 
  → (Maybe ∘ List) (List ((Σ Index (ℒ ∘ ⟦_⟧)) ⊎ (Σ Index (Dual ∘ ⟦_⟧ℒ))))
chooseSolver NatI = unifyDisunify NatI
--chooseSolver (×I x) = unifyDisunify (×I x)
--chooseSolver (ListI x) = unifyDisunify (ListI x)

instance  solver : Solver Index ⟦_⟧ ⟦_⟧ℒ
          solver .solve = chooseSolver
-}
module program where
  open Term.types

  -- ---------------------------------------------------------------------
  -- Example program
  dupliProgram : (i : Index) → ⦃ MakeVar ⟦ i ⟧ ⦄ → Clause (Functor ⟦ i ⟧) validate Index ⟦_⟧ℒ
  dupliProgram i = do

    not (dupli [] []) •

    X ← new
    Xs ← new
    Ys ← new

    dupli (X ∷ Xs) (X ∶ X ∷ Ys) :-
      dupli Xs Ys ∧
      idC X X ∧
      (ListI i , Xs ≥List Xs) ↼•
      -- dupli Xs Ys •

  test = applyVars (dupliProgram NatI) 0