module Term.streamreasoning where

open import Data.Bool hiding (_≟_ ; _∧_ ; not)
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
open import ASP.types
open import Bool.domain
open import FD.domain
open import Sum.domain

data My𝒞 : Set where
  Bool𝒞  : My𝒞
  FD𝒞  : My𝒞
  ⊎𝒞 : (c₀ : My𝒞) → (c₁ : My𝒞) → My𝒞

⟦_⟧ : My𝒞 → Set
⟦ Bool𝒞 ⟧    = BoolLogic
⟦ FD𝒞 ⟧    = FD
⟦ ⊎𝒞 c₀ c₁ ⟧    = ⊎Logic ⟦ c₀ ⟧ ⟦ c₁ ⟧

⟦_⟧ℒ : My𝒞 → Set
⟦ Bool𝒞 ⟧ℒ    = ⊥
⟦ FD𝒞 ⟧ℒ    = ℒFD
⟦ ⊎𝒞 c₀ c₁ ⟧ℒ  = ⊥

mapType : (c : My𝒞) → FTUtils ⟦ c ⟧
mapType Bool𝒞        = ftUtilsBool
mapType FD𝒞        = ftUtilsFD
mapType (⊎𝒞 c₀ c₁) = ftUtils⊎  ⦃ mapType c₀ ⦄  ⦃ mapType c₁ ⦄

mapConstraint : (c : My𝒞) → FTUtils ⟦ c ⟧ℒ
mapConstraint Bool𝒞 = record {}
mapConstraint FD𝒞        = ftUtilsℒFD
mapConstraint (⊎𝒞 c₀ c₁) = record {}

indexD : HasDesc My𝒞
indexD = deriveDesc My𝒞

instance  decMy𝒞 : DecEq My𝒞
          decMy𝒞 = deriveDecEq indexD

data Functor : Set where
  fnot    : Functor → Functor
  validStream : FD → ⊎Logic BoolLogic BoolLogic → Functor
  stream : FD → ⊎Logic BoolLogic BoolLogic → Functor
  cancelled : FD → ⊎Logic BoolLogic BoolLogic → Functor
  higherPrio : FD → FD → Functor
  incompt : ⊎Logic BoolLogic BoolLogic → ⊎Logic BoolLogic BoolLogic → Functor
  ffalse  : Functor

functorD : HasDesc Functor
functorD = deriveDesc Functor

foldFunctor = deriveFold functorD

validate : Where → Functor → Set
validate _ (fnot _) = ⊤
validate _ ffalse = ⊤
validate _ _ = ⊤

instance  aspUtils : ASPUtils Functor
          aspUtils .not = fnot
          aspUtils .isNot (fnot _) = true
          aspUtils .isNot _ = false

instance  constraintUtils : ConstraintUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          constraintUtils .increment Bool𝒞 _ ()
          constraintUtils .increment FD𝒞 = incrementℒFD
          constraintUtils .increment (⊎𝒞 c₀ c₁) _ ()
          constraintUtils .apply Bool𝒞 Bool𝒞 _ _ ()
          constraintUtils .apply FD𝒞 FD𝒞 = applyℒFD
          constraintUtils .apply _ (⊎𝒞 c₀ c₁) _ _ ()
          constraintUtils .apply _ _ _ _ expr = expr

instance  valueUtils : ValueUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          valueUtils .zipMatch Bool𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ Bool𝒞 l ⦃ ftUtilsBool ⦄ ⦃ _ ⦄ ⦃ record {} ⦄)) ∘ zipMatchBool c
          valueUtils .zipMatch FD𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ FD𝒞 l ⦃ ftUtilsFD ⦄ ⦃ _ ⦄ ⦃ ftUtilsℒFD ⦄)) ∘ zipMatchFD c
          valueUtils .zipMatch (⊎𝒞 c₀ c₁) = zipMatch⊎ c₀ c₁ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ mapType c₀ ⦄ ⦃ mapConstraint c₀ ⦄ ⦃ mapType c₁ ⦄ ⦃ mapConstraint c₁ ⦄
          valueUtils .increment Bool𝒞 = incrementBool
          valueUtils .increment FD𝒞 = incrementFD
          valueUtils .increment (⊎𝒞 c₀ c₁) = increment⊎
          valueUtils .apply Bool𝒞 Bool𝒞 = applyBool
          valueUtils .apply FD𝒞 FD𝒞 = applyFD
          valueUtils .apply (⊎𝒞 c₀ c₁) (⊎𝒞 c₀ c₁) = apply⊎ i₀ i₁
          valueUtils .apply i₀ Bool𝒞 n subst expr = expr
          valueUtils .apply i₀ FD𝒞 n subst expr = expr
          valueUtils .apply i₀ (⊎𝒞 c₀ c₁) n subst = 
            fold⊎ 
              (λ x → p (apply i₀ (⊎𝒞 c₀ c₁) n subst x)) 
              (λ x → q (apply i₀ (⊎𝒞 c₀ c₁) n subst x))

instance  atomUtils : AtomUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch fnot fnot = just []
          atomUtils .zipMatch (validStream a b) (validStream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞) (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (stream a b) (stream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞) (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (cancelled a b) (cancelled x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞) (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (higherPrio a b) (higherPrio x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (incompt a b) (incompt x y) = 
            just ((_:-:_ (⊎𝒞 Bool𝒞) (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞) (b =ℒ y)) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a b → validStream (incrementFD n a) (incrementBool n b))
              (λ a b → stream (incrementFD n a) (incrementBool n b))
              (λ a b → cancelled (incrementFD n a) (incrementBool n b))
              (λ a b → higherPrio (incrementFD n a) (incrementFD n b))
              (λ a b → incompt (incrementBool n a) (incrementBool n b))
              ffalse

instance  solver : Solver My𝒞 ⟦_⟧ ⟦_⟧ℒ
          solver .solve = unifyDisunify

instance  scheduler : Scheduler My𝒞 ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ decMy𝒞 ⦄ ⦃ solver ⦄

module program where
  open Term.types

  streamReasoning :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  streamReasoning = do
    P ← new
    Data ← new

    validStream P Data :-
        stream P Data
      ∧  not (cancelled P Data) •
    
    P1 ← new
    Data1 ← new

    cancelled P Data :-
        higherPrio P1 P
      ∧  stream P1 Data1
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

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    validStream (varFD 0) (var⊎ 1) •

  execute = clpExecute id id streamReasoning question false