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
open import Empty.domain
open import Bool.domain
open import FD.domain
open import Sum.domain

open import ASP.types
open import ASP.asp

open import Term.domainUniverseGeneration hiding (_>>=_ ; _>>_)

unquoteDecl data My𝒞 constructor Bool𝒞 FD𝒞 ⊎𝒞 =
  makeUniverse
    My𝒞
    ( (Bool𝒞 , quote BoolLogic) ∷
      (FD𝒞   , quote FD       ) ∷
      (⊎𝒞    , quote ⊎Logic   ) ∷ [] )

unquoteDecl ⟦_⟧ =
  makeDecoder ⟦_⟧ (quote My𝒞)
    ( (quote Bool𝒞 , quote BoolLogic) ∷
      (quote FD𝒞   , quote FD      ) ∷
      (quote ⊎𝒞     , quote ⊎Logic ) ∷
      [] )

⟦_⟧ℒ : My𝒞 → Set
⟦ Bool𝒞 ⟧ℒ    = ⊥
⟦ FD𝒞 ⟧ℒ    = ℒFD
⟦ ⊎𝒞 c₀ c₁ ⟧ℒ  = ⊥

unquoteDecl mapType =
  makeMapper mapType (quote My𝒞) (quote ⟦_⟧) (quote FTUtils)
    ( (quote Bool𝒞 , quote ftUtilsBool) ∷
      (quote FD𝒞   , quote ftUtilsFD  ) ∷
      (quote ⊎𝒞    , quote ftUtils⊎   ) ∷ [] )

mapConstraint : (c : My𝒞) → FTUtils ⟦ c ⟧ℒ
mapConstraint Bool𝒞 = ftUtils⊥
mapConstraint FD𝒞        = ftUtilsℒFD
mapConstraint (⊎𝒞 c₀ c₁) = ftUtils⊥

unquoteDecl mapDecEq =
  makeMapper mapDecEq (quote My𝒞) (quote ⟦_⟧) (quote DecEq)
    ( (quote Bool𝒞 , quote decBool) ∷
      (quote FD𝒞   , quote decFD  ) ∷
      (quote ⊎𝒞    , quote dec⊎   ) ∷ [] )

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

instance  ftUtilsFunctor : FTUtils Functor
          ftUtilsFunctor = deriveFTUtils functorD

foldFunctor = deriveFold functorD

validate : Where → Functor → Set
validate _ (fnot _) = ⊤
validate _ ffalse = ⊤
validate _ _ = ⊤

instance  aspUtils : ASPUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          aspUtils .not = fnot
          aspUtils .isNot (fnot _) = true
          aspUtils .isNot _ = false
          aspUtils .isFalse ffalse = true
          aspUtils .isFalse _ = false
          aspUtils .toggle (fnot x) = x
          aspUtils .toggle x = fnot x
          aspUtils .fillWithVars _ = {!   !}

instance  constraintUtils : ConstraintUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          constraintUtils .zipMatch Bool𝒞 ()
          constraintUtils .zipMatch FD𝒞 = {!   !}
          constraintUtils .zipMatch (⊎𝒞 c₀ c₁) ()
          constraintUtils .increment Bool𝒞 _ ()
          constraintUtils .increment FD𝒞 = incrementℒFD
          constraintUtils .increment (⊎𝒞 c₀ c₁) _ ()
          constraintUtils .apply Bool𝒞 Bool𝒞 _ _ ()
          constraintUtils .apply FD𝒞 FD𝒞 = applyℒFD
          constraintUtils .apply _ (⊎𝒞 c₀ c₁) _ _ ()
          constraintUtils .apply _ _ _ _ expr = expr

instance  valueUtils : ValueUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          valueUtils .zipMatch Bool𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ Bool𝒞 l ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄)) ∘ zipMatchBool c
          valueUtils .zipMatch FD𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ FD𝒞 l ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄)) ∘ zipMatchFD c
          valueUtils .zipMatch (⊎𝒞 c₀ c₁) = zipMatch⊎ c₀ c₁ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ mapType c₀ ⦄ ⦃ mapConstraint c₀ ⦄ ⦃ mapDecEq c₀ ⦄ ⦃ mapType c₁ ⦄ ⦃ mapConstraint c₁ ⦄ ⦃ mapDecEq c₁ ⦄
          valueUtils .increment Bool𝒞 = incrementBool
          valueUtils .increment FD𝒞 = incrementFD
          valueUtils .increment (⊎𝒞 c₀ c₁) = increment⊎
          valueUtils .apply Bool𝒞 Bool𝒞 = applyBool
          valueUtils .apply FD𝒞 FD𝒞 = applyFD
          valueUtils .apply (⊎𝒞 c₀ c₁) (⊎𝒞 c₂ c₃) = apply⊎ c₀ c₁ c₂ c₃ (apply valueUtils (⊎𝒞 c₀ c₁) c₂) (apply valueUtils (⊎𝒞 c₀ c₁) c₃)
          valueUtils .apply i₀ Bool𝒞 n subst expr = expr
          valueUtils .apply i₀ FD𝒞 n subst expr = expr
          valueUtils .apply i₀ (⊎𝒞 c₀ c₁) n subst = 
            fold⊎ 
              (λ x → p (apply valueUtils i₀ c₀ n subst x)) 
              (λ x → q (apply valueUtils i₀ c₁ n subst x))
              var⊎

instance  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch (fnot x) (fnot y) = zipMatch atomUtils x y
          atomUtils .zipMatch (validStream a b) (validStream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch (stream a b) (stream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch (cancelled a b) (cancelled x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch (higherPrio a b) (higherPrio x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (incompt a b) (incompt x y) = 
            just ((_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (a =ℒ x) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a b → validStream (incrementFD n a) (increment⊎ n b))
              (λ a b → stream (incrementFD n a) (increment⊎ n b))
              (λ a b → cancelled (incrementFD n a) (increment⊎ n b))
              (λ a b → higherPrio (incrementFD n a) (incrementFD n b))
              (λ a b → incompt (increment⊎ n a) (increment⊎ n b))
              ffalse

instance  solver : Solver My𝒞 ⟦_⟧ ⟦_⟧ℒ
          solver .solve Bool𝒞 = unifyDisunify Bool𝒞 ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄
          solver .solve FD𝒞 = {! !}
          solver .solve (⊎𝒞 c₀ c₁) = unifyDisunify (⊎𝒞 c₀ c₁) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄

instance  scheduler : Scheduler My𝒞 ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ _ ⦄ ⦃ _ ⦄

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
      (◇ (FD𝒞 :-: (PHi ＃> PLo))) ↼•
    
    X ← new

    incompt (p X) (q X) •
    incompt (q X) (p X) •

    stream zero (p X) •
    stream (suc zero) (q true) •
    stream (suc (suc zero)) (q false) •
    stream (suc (suc (suc zero))) (p true) •

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    validStream (varFD 0) (var⊎ 1) •

  execute = aspExecute streamReasoning question