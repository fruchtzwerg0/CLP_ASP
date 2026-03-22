module Examples.myDomainGroup where

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

open import CLP.ftUtilsDerivation
open import CLP.types
open import CLP.unifyDisunify
open import CLP.solverScheduler
open import CLP.clp
open import CLP.utilities
open import Empty.domain
open import Bool.domain
open import FD.domain
open import FD.solver
open import Sum.domain
open import Product.domain
open import List.domain

open import CLP.domainUniverseGeneration hiding (_>>=_ ; _>>_)

-- In here, an example domain group is created, outlining the steps needed to be taken for it to be usable.

-- The first step is deriving the universe code type. The name My𝒞 will be the name of the type, and Bool𝒞 FD𝒞 ⊎𝒞
-- will be the constructors. The last parameter maps codes to actual types you want to use.
unquoteDecl data My𝒞 constructor Bool𝒞 FD𝒞 ⊎𝒞 ×𝒞 list𝒞 =
  makeUniverse
    My𝒞
    ( (Bool𝒞 , quote BoolLogic) ∷
      (FD𝒞   , quote FD       ) ∷
      (⊎𝒞    , quote ⊎Logic   ) ∷
      (×𝒞    , quote ×Logic   ) ∷
      (list𝒞 , quote ListLogic) ∷ [] )

-- For the universe to be usable, we need to derive a decoder function. The parameters stay thet same, but we need to quote 
-- the things we already have.
unquoteDecl ⟦_⟧ =
  makeDecoder ⟦_⟧ (quote My𝒞)
    ( (quote Bool𝒞 , quote BoolLogic) ∷
      (quote FD𝒞   , quote FD      ) ∷
      (quote ⊎𝒞    , quote ⊎Logic ) ∷
      (quote ×𝒞    , quote ×Logic   ) ∷
      (quote list𝒞 , quote ListLogic   ) ∷
      [] )

-- The mapper from code to constraint type we need to define manually.
-- In this case, Bool𝒞 and ⊎𝒞 don't have constraint domains, therefore we provide the bottom type.
-- FD has the ℒFD constraint type.
⟦_⟧ℒ : My𝒞 → Set
⟦ Bool𝒞 ⟧ℒ    = ⊥
⟦ FD𝒞 ⟧ℒ    = ℒFD
⟦ ⊎𝒞 c₀ c₁ ⟧ℒ  = ⊥
⟦ ×𝒞 c₀ c₁ ⟧ℒ  = ⊥
⟦ list𝒞 c ⟧ℒ  = ⊥

-- Helper function we need for the definition of zipMatch for ⊎𝒞
unquoteDecl mapType =
  makeMapper mapType (quote My𝒞) (quote ⟦_⟧) (quote FTUtils)
    ( (quote Bool𝒞 , quote ftUtilsBool) ∷
      (quote FD𝒞   , quote ftUtilsFD  ) ∷
      (quote ⊎𝒞    , quote ftUtils⊎   ) ∷
      (quote ×𝒞    , quote ftUtils×   ) ∷
      (quote list𝒞    , quote ftUtilsList   ) ∷ [] )

-- Helper function we need for the definition of zipMatch for ⊎𝒞
mapConstraint : (c : My𝒞) → FTUtils ⟦ c ⟧ℒ
mapConstraint Bool𝒞 = ftUtils⊥
mapConstraint FD𝒞        = ftUtilsℒFD
mapConstraint (⊎𝒞 c₀ c₁) = ftUtils⊥
mapConstraint (×𝒞 c₀ c₁) = ftUtils⊥
mapConstraint (list𝒞 c) = ftUtils⊥

-- Helper function we need for the definition of zipMatch for ⊎𝒞
unquoteDecl mapDecEq =
  makeMapper mapDecEq (quote My𝒞) (quote ⟦_⟧) (quote DecEq)
    ( (quote Bool𝒞 , quote decBool) ∷
      (quote FD𝒞   , quote decFD  ) ∷
      (quote ⊎𝒞    , quote dec⊎   ) ∷
      (quote ×𝒞    , quote dec×   ) ∷
      (quote list𝒞    , quote decList   ) ∷ [] )

indexD : HasDesc My𝒞
indexD = deriveDesc My𝒞

-- We need decidable equality for our universe type.
instance  decMy𝒞 : DecEq My𝒞
          decMy𝒞 = deriveDecEq indexD

-- We need to provide constraint utilities for all the constraint types in our universe.
-- These are provided in the same file of the domains, so we just need to glue it together.
instance  constraintUtils : ConstraintUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          constraintUtils .zipMatch Bool𝒞 ()
          constraintUtils .zipMatch FD𝒞 c = 
            Data.Maybe.map (Data.List.map (λ l → _:-:_ FD𝒞 l ⦃ ftUtilsFD ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ decFD ⦄)) ∘ zipMatchℒFD c
          constraintUtils .zipMatch (⊎𝒞 c₀ c₁) ()
          constraintUtils .zipMatch (×𝒞 c₀ c₁) ()
          constraintUtils .increment Bool𝒞 _ ()
          constraintUtils .increment FD𝒞 = incrementℒFD
          constraintUtils .increment (⊎𝒞 c₀ c₁) _ ()
          constraintUtils .increment (×𝒞 c₀ c₁) _ ()
          constraintUtils .apply Bool𝒞 Bool𝒞 _ _ ()
          constraintUtils .apply FD𝒞 FD𝒞 = applyℒFD
          constraintUtils .apply _ (⊎𝒞 c₀ c₁) _ _ ()
          constraintUtils .apply _ (×𝒞 c₀ c₁) _ _ ()
          constraintUtils .apply _ _ _ _ expr = expr

-- We need to provide value utilities for all the domain types in our universe.
-- These are provided in the same file of the domains, so we just need to glue it together.
instance  valueUtils : ValueUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          valueUtils .zipMatch Bool𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ Bool𝒞 l ⦃ ftUtilsBool ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decBool ⦄)) ∘ zipMatchBool c
          valueUtils .zipMatch FD𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ FD𝒞 l ⦃ ftUtilsFD ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ decFD ⦄)) ∘ zipMatchFD c
          valueUtils .zipMatch (⊎𝒞 c₀ c₁) = zipMatch⊎ c₀ c₁ ⦃ mapType c₀ ⦄ ⦃ mapConstraint c₀ ⦄ ⦃ mapDecEq c₀ ⦄ ⦃ mapType c₁ ⦄ ⦃ mapConstraint c₁ ⦄ ⦃ mapDecEq c₁ ⦄
          valueUtils .zipMatch (×𝒞 c₀ c₁) = zipMatch× c₀ c₁ ⦃ mapType c₀ ⦄ ⦃ mapConstraint c₀ ⦄ ⦃ mapDecEq c₀ ⦄ ⦃ mapType c₁ ⦄ ⦃ mapConstraint c₁ ⦄ ⦃ mapDecEq c₁ ⦄
          valueUtils .zipMatch (list𝒞 c) x = 
            Data.Maybe.map (λ { (x , y) → x ++ Data.List.map (λ l → _:-:_ (list𝒞 c) l ⦃ ftUtilsList ⦃ mapType c ⦄ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦃ mapDecEq c ⦄ ⦄) y }) 
            ∘ zipMatchList c ⦃ mapType c ⦄ ⦃ mapConstraint c ⦄ ⦃ mapDecEq c ⦄ x
          valueUtils .increment Bool𝒞 = incrementBool
          valueUtils .increment FD𝒞 = incrementFD
          valueUtils .increment (⊎𝒞 c₀ c₁) = increment⊎
          valueUtils .increment (×𝒞 c₀ c₁) = increment×
          valueUtils .increment (list𝒞 c) = incrementList
          valueUtils .apply Bool𝒞 Bool𝒞 = applyBool
          valueUtils .apply FD𝒞 FD𝒞 = applyFD
          valueUtils .apply (⊎𝒞 c₀ c₁) (⊎𝒞 c₂ c₃) = apply⊎ c₀ c₁ c₂ c₃ (apply valueUtils (⊎𝒞 c₀ c₁) c₂) (apply valueUtils (⊎𝒞 c₀ c₁) c₃)
          valueUtils .apply (×𝒞 c₀ c₁) (×𝒞 c₂ c₃) = apply× c₀ c₁ c₂ c₃ (apply valueUtils (×𝒞 c₀ c₁) c₂) (apply valueUtils (×𝒞 c₀ c₁) c₃)
          valueUtils .apply (list𝒞 c₀) (list𝒞 c₁) = applyList c₀ c₁ (apply valueUtils (list𝒞 c₀) c₁)
          valueUtils .apply i₀ Bool𝒞 n subst expr = expr
          valueUtils .apply i₀ FD𝒞 n subst expr = expr
          valueUtils .apply i₀ (⊎𝒞 c₀ c₁) n subst = 
            fold⊎ 
              (λ x → p (apply valueUtils i₀ c₀ n subst x)) 
              (λ x → q (apply valueUtils i₀ c₁ n subst x))
              var⊎
          valueUtils .apply i₀ (×𝒞 c₀ c₁) n subst = 
            fold× 
              (λ x y → apply valueUtils i₀ c₀ n subst x ∶ apply valueUtils i₀ c₁ n subst y) 
              var×
          valueUtils .apply i₀ (list𝒞 c) n subst [] = []
          valueUtils .apply i₀ (list𝒞 c) n subst (varList x) = varList x
          valueUtils .apply i₀ (list𝒞 c) n subst (x ∷ xs) = (apply valueUtils i₀ c n subst x) ∷ (apply valueUtils i₀ (list𝒞 c) n subst xs)

-- Here, we can use pattern matching to map domains to solvers. 
-- unifyDisunify is part of the abstract CLP scheme, and domain-agnostic.
-- Therefore it can be used for any domain and acts as a catch-all when we don't have any domain specific solver, 
-- and if we don't have a custom constraint domain.
-- FD has its own solver. Here, it needs to be converted back to the general dependent type.
instance  solver : Solver My𝒞 ⟦_⟧ ⟦_⟧ℒ
          solver .solve Bool𝒞 = unifyDisunify Bool𝒞 ⦃ decMy𝒞 ⦄ ⦃ ftUtilsBool ⦄ ⦃ valueUtils ⦄ ⦃ ftUtils⊥ ⦄ ⦃ constraintUtils ⦄
          solver .solve FD𝒞 = 
            Data.List.map (Data.List.map 
              (λ {(inj₁ x) → inj₁ (generalize FD𝒞 ⦃ ftUtilsFD ⦄ ⦃ valueUtils ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ constraintUtils ⦄ ⦃ decFD ⦄ x) ; 
                  (inj₂ x) → inj₂ (generalizeCustom FD𝒞 ⦃ ftUtilsFD ⦄ ⦃ valueUtils ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ constraintUtils ⦄ ⦃ decFD ⦄ x)})) ∘ fdSolve
          solver .solve (⊎𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify (⊎𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ dec⊎ ⦃ mapDecEq c₀ ⦄ ⦃ mapDecEq c₁ ⦄ ⦄
          solver .solve (×𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify (×𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ dec× ⦃ mapDecEq c₀ ⦄ ⦃ mapDecEq c₁ ⦄ ⦄
          solver .solve (list𝒞 c) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify (list𝒞 c) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ decList ⦃ mapDecEq c ⦄ ⦄

-- It is not recommended to modify the scheduler, defaultSchedule is perfectly safe and usable for any domain group.
instance  scheduler : Scheduler My𝒞 ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ decMy𝒞 ⦄ ⦃ valueUtils ⦄ ⦃ constraintUtils ⦄ ⦃ solver ⦄