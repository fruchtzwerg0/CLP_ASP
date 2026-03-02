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

data My𝒞 : Set where
  Bool𝒞  : My𝒞
  FT𝒞  : My𝒞
  ⊎𝒞 : (c₀ : My𝒞) → (c₁ : My𝒞) → My𝒞

⟦_⟧ : My𝒞 → Set
⟦ Bool𝒞 ⟧    = BoolLogic
⟦ FD𝒞 ⟧    = ℕLogic
⟦ ⊎𝒞 c₀ c₁ ⟧    = ⊎Logic ⟦ c₀ ⟧ ⟦ c₁ ⟧

⟦_⟧ℒ : My𝒞 → Set
⟦ Bool𝒞 ⟧ℒ    = ⊥
⟦ Nat𝒞 ⟧ℒ    = ℒℕ
⟦ ⊎𝒞 c₀ c₁ ⟧ℒ  = ⊥

indexD : HasDesc My𝒞
indexD = deriveDesc My𝒞

instance  decMy𝒞 : DecEq My𝒞
          decMy𝒞 = deriveDecEq indexD

data Functor : Set where
  fnot    : Functor → Functor
  validStream : FD → ⊎Logic BoolLogic → Functor
  stream : FD → ⊎Logic BoolLogic → Functor
  cancelled : FD → ⊎Logic BoolLogic → Functor
  higherPrio : FD → FD → Functor
  incompt : ⊎Logic BoolLogic → ⊎Logic BoolLogic → Functor
  ffalse  : Functor

functorD : HasDesc Functor
functorD = deriveDesc Functor

foldFunctor = deriveFold functorD

validate : ∀ {A} → Where → AbstractOrConcrete → Functor A → Set
validate _ abstr (fnot _) = ⊤
validate bodyOfRule concr (fnot _) = ⊤
validate _ _ (dupli _ _) = ⊤
validate bodyOfRule _ ftrue = ⊤
validate _ _ ffalse = ⊤
validate _ _ _ = ⊤

instance  aspUtils : ASPUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          aspUtils .not = fnot
          aspUtils .isNot (fnot _) = true
          aspUtils .isNot _ = false

instance  constraintUtils : ConstraintUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          constraintUtils .increment Bool𝒞 _ ()
          constraintUtils .increment FD𝒞 = incrementℒFD
          constraintUtils .increment (⊎𝒞 i) _ ()
          constraintUtils .apply Bool𝒞 _ _ _ ()
          constraintUtils .apply FD𝒞 = applyℒFD
          constraintUtils .apply (⊎𝒞 i) _ _ _ ()

instance  valueUtils : ValueUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          valueUtils .zipMatch Bool𝒞 = zipMatchBool
          valueUtils .zipMatch FD𝒞 = zipMatchFD
          valueUtils .zipMatch (⊎𝒞 i) = zipMatch⊎
          valueUtils .increment Bool𝒞 = incrementBool
          valueUtils .increment FD𝒞 = incrementFD
          valueUtils .increment (⊎𝒞 i) = increment⊎
          valueUtils .apply Bool𝒞 Bool𝒞 = applyBool
          valueUtils .apply FD𝒞 FD𝒞 = applyFD
          valueUtils .apply (⊎𝒞 i₀) (⊎𝒞 i₁) = applyFD
          valueUtils .apply i₀ Bool𝒞 n subst expr = expr
          valueUtils .apply i₀ FD𝒞 n subst expr = expr
          valueUtils .apply i₀ (⊎𝒞 i₁ i₂) n subst = 
            fold⊎ 
              (λ x → p (apply i₀ (⊎𝒞 i₁ i₂) n subst x)) 
              (λ x → q (apply i₀ (⊎𝒞 i₁ i₂) n subst x))

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
    Body (Functor ℕLogic) (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    hanoiMoves (suc (suc (suc zero))) (varList 0) •

  execute = eval (zipAtom NatI) zipValue ((toIntern ∘ proj₂) groundProgram) (toLiteralList question) [] false