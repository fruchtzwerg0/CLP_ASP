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
open import Nat.domain
open import String.domain

open import CLP.domainUniverseGeneration hiding (_>>=_ ; _>>_)

-- In here, an example domain group is created, outlining the steps needed to be taken for it to be usable.

-- The first step is deriving the universe code type. The name My𝒞 will be the name of the type, and bool𝒞 fd𝒞 ⊎𝒞
-- will be the constructors. The last parameter maps codes to actual types you want to use.
unquoteDecl data My𝒞 constructor bool𝒞 fd𝒞 ⊎𝒞 ×𝒞 list𝒞 nat𝒞 string𝒞 =
  makeUniverse
    My𝒞
    ( (bool𝒞 , quote BoolLogic) ∷
      (fd𝒞   , quote FD       ) ∷
      (⊎𝒞    , quote ⊎Logic   ) ∷
      (×𝒞    , quote ×Logic   ) ∷
      (list𝒞 , quote ListLogic) ∷
      (nat𝒞    , quote NatLogic   ) ∷
      (string𝒞 , quote StringLogic) ∷ [] )

-- For the universe to be usable, we need to derive a decoder function. The parameters stay thet same, but we need to quote 
-- the things we already have.
unquoteDecl ⟦_⟧ =
  makeDecoder ⟦_⟧ (quote My𝒞)
    ( (quote bool𝒞 , quote BoolLogic) ∷
      (quote fd𝒞   , quote FD      ) ∷
      (quote ⊎𝒞    , quote ⊎Logic ) ∷
      (quote ×𝒞    , quote ×Logic   ) ∷
      (quote list𝒞 , quote ListLogic   ) ∷
      (quote nat𝒞    , quote NatLogic   ) ∷
      (quote string𝒞 , quote StringLogic) ∷ 
      [] )

-- The mapper from code to constraint type we need to define manually.
-- In this case, bool𝒞 and ⊎𝒞 don't have constraint domains, therefore we provide the bottom type.
-- FD has the ℒFD constraint type.
⟦_⟧ℒ : My𝒞 → Set
⟦ bool𝒞 ⟧ℒ    = ⊥
⟦ fd𝒞 ⟧ℒ    = ℒFD
⟦ ⊎𝒞 c₀ c₁ ⟧ℒ  = ⊥
⟦ ×𝒞 c₀ c₁ ⟧ℒ  = ⊥
⟦ list𝒞 c ⟧ℒ  = ⊥
⟦ nat𝒞 ⟧ℒ  = ⊥
⟦ string𝒞 ⟧ℒ  = ⊥

-- Helper function we need for the definition of zipMatch for ⊎𝒞
unquoteDecl mapType =
  makeMapper mapType (quote My𝒞) (quote ⟦_⟧) (quote FTUtils)
    ( (quote bool𝒞 , quote ftUtilsBool) ∷
      (quote fd𝒞   , quote ftUtilsFD  ) ∷
      (quote ⊎𝒞    , quote ftUtils⊎   ) ∷
      (quote ×𝒞    , quote ftUtils×   ) ∷
      (quote list𝒞    , quote ftUtilsList   ) ∷ 
      (quote nat𝒞    , quote ftUtilsNat   ) ∷
      (quote string𝒞 , quote ftUtilsString) ∷ [] )

-- Helper function we need for the definition of zipMatch for ⊎𝒞
mapConstraint : (c : My𝒞) → FTUtils ⟦ c ⟧ℒ
mapConstraint bool𝒞 = ftUtils⊥
mapConstraint fd𝒞        = ftUtilsℒFD
mapConstraint (⊎𝒞 c₀ c₁) = ftUtils⊥
mapConstraint (×𝒞 c₀ c₁) = ftUtils⊥
mapConstraint (list𝒞 c) = ftUtils⊥
mapConstraint nat𝒞 = ftUtils⊥
mapConstraint string𝒞 = ftUtils⊥

-- Helper function we need for the definition of zipMatch for ⊎𝒞
unquoteDecl mapDecEq =
  makeMapper mapDecEq (quote My𝒞) (quote ⟦_⟧) (quote DecEq)
    ( (quote bool𝒞 , quote decBool) ∷
      (quote fd𝒞   , quote decFD  ) ∷
      (quote ⊎𝒞    , quote dec⊎   ) ∷
      (quote ×𝒞    , quote dec×   ) ∷
      (quote list𝒞    , quote decList   ) ∷ 
      (quote nat𝒞    , quote decNat   ) ∷
      (quote string𝒞 , quote decString) ∷ [] )

-- Helper function we need for the definition of zipMatch for ⊎𝒞
mapMakeVar : (c : My𝒞) → MakeVar ⟦ c ⟧
mapMakeVar bool𝒞 = makeVarBool
mapMakeVar fd𝒞        = makeVarFD
mapMakeVar (⊎𝒞 c₀ c₁) = makeVar⊎
mapMakeVar (×𝒞 c₀ c₁) = makeVar×
mapMakeVar (list𝒞 c) = makeVarList
mapMakeVar nat𝒞 = makeVarNat
mapMakeVar string𝒞 = makeVarString

-- Helper function we need for the definition of zipMatch for ⊎𝒞
unquoteDecl mapShow =
  makeMapper mapShow (quote My𝒞) (quote ⟦_⟧) (quote Show)
    ( (quote bool𝒞 , quote showBool) ∷
      (quote fd𝒞   , quote showFD  ) ∷
      (quote ⊎𝒞    , quote show⊎   ) ∷
      (quote ×𝒞    , quote show×   ) ∷
      (quote list𝒞    , quote showList   ) ∷ 
      (quote nat𝒞    , quote showNat   ) ∷
      (quote string𝒞    , quote showString   ) ∷ [] )

-- Helper function we need for the definition of zipMatch for ⊎𝒞
mapShowConstraint : (c : My𝒞) → Show ⟦ c ⟧ℒ
mapShowConstraint bool𝒞 .show ()
mapShowConstraint fd𝒞        = showℒFD
mapShowConstraint (⊎𝒞 c₀ c₁) .show ()
mapShowConstraint (×𝒞 c₀ c₁) .show ()
mapShowConstraint (list𝒞 c) .show ()
mapShowConstraint nat𝒞 .show ()
mapShowConstraint string𝒞 .show ()

indexD : HasDesc My𝒞
indexD = deriveDesc My𝒞

-- We need decidable equality for our universe type.
instance  decMy𝒞 : DecEq My𝒞
          decMy𝒞 = deriveDecEq indexD

-- We need to provide constraint utilities for all the constraint types in our universe.
-- These are provided in the same file of the domains, so we just need to glue it together.
instance  constraintUtils : ConstraintUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          constraintUtils .zipMatch fd𝒞 c = 
            Data.Maybe.map (Data.List.map (λ l → _:-:_ fd𝒞 l)) ∘ zipMatchℒFD c
          constraintUtils .increment fd𝒞 = incrementℒFD
          constraintUtils .apply fd𝒞 fd𝒞 = applyℒFD
          constraintUtils .apply _ _ _ _ expr = expr

-- We need to provide value utilities for all the domain types in our universe.
-- These are provided in the same file of the domains, so we just need to glue it together.
instance  valueUtils : ValueUtils My𝒞 ⟦_⟧ ⟦_⟧ℒ
          valueUtils .zipMatch bool𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ bool𝒞 l ⦃ ftUtilsBool ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decBool ⦄ ⦃ makeVarBool ⦄ ⦃ mapShow bool𝒞 ⦄ ⦃ mapShowConstraint bool𝒞 ⦄)) ∘ zipMatchBool c
          valueUtils .zipMatch fd𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ fd𝒞 l ⦃ ftUtilsFD ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ decFD ⦄)) ∘ zipMatchFD c
          valueUtils .zipMatch (⊎𝒞 c₀ c₁) = zipMatch⊎ c₀ c₁ ⦃ mapType c₀ ⦄ ⦃ mapConstraint c₀ ⦄ ⦃ mapDecEq c₀ ⦄ ⦃ mapMakeVar c₀ ⦄ ⦃ mapShow c₀ ⦄ ⦃ mapShowConstraint c₀ ⦄ ⦃ mapType c₁ ⦄ ⦃ mapConstraint c₁ ⦄ ⦃ mapDecEq c₁ ⦄ ⦃ mapMakeVar c₁ ⦄ ⦃ mapShow c₁ ⦄ ⦃ mapShowConstraint c₁ ⦄
          valueUtils .zipMatch (×𝒞 c₀ c₁) = zipMatch× c₀ c₁ ⦃ mapType c₀ ⦄ ⦃ mapConstraint c₀ ⦄ ⦃ mapDecEq c₀ ⦄ ⦃ mapMakeVar c₀ ⦄ ⦃ mapShow c₀ ⦄ ⦃ mapShowConstraint c₀ ⦄ ⦃ mapType c₁ ⦄ ⦃ mapConstraint c₁ ⦄ ⦃ mapDecEq c₁ ⦄ ⦃ mapMakeVar c₁ ⦄ ⦃ mapShow c₁ ⦄ ⦃ mapShowConstraint c₁ ⦄
          valueUtils .zipMatch (list𝒞 c) x = 
            Data.Maybe.map (λ { (x , y) → x ++ Data.List.map (λ l → _:-:_ (list𝒞 c) l ⦃ ftUtilsList ⦃ mapType c ⦄ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦃ mapDecEq c ⦄ ⦄ ⦃ mapMakeVar (list𝒞 c) ⦄ ⦃ showList ⦃ mapShow c ⦄ ⦄ ⦃ mapShowConstraint (list𝒞 c) ⦄) y }) 
            ∘ zipMatchList c ⦃ mapType c ⦄ ⦃ mapConstraint c ⦄ ⦃ mapDecEq c ⦄ ⦃ mapMakeVar c ⦄ ⦃ mapShow c ⦄ ⦃ mapShowConstraint c ⦄ x
          valueUtils .zipMatch nat𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ nat𝒞 l ⦃ ftUtilsNat ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decNat ⦄ ⦃ makeVarNat ⦄ ⦃ mapShow nat𝒞 ⦄ ⦃ mapShowConstraint nat𝒞 ⦄)) ∘ zipMatchNat c
          valueUtils .zipMatch string𝒞 c = Data.Maybe.map (Data.List.map (λ l → _:-:_ string𝒞 l ⦃ ftUtilsString ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decString ⦄)) ∘ zipMatchString c
          valueUtils .increment bool𝒞 = incrementBool
          valueUtils .increment fd𝒞 = incrementFD
          valueUtils .increment (⊎𝒞 c₀ c₁) = increment⊎ (increment valueUtils c₀) (increment valueUtils c₁)
          valueUtils .increment (×𝒞 c₀ c₁) = increment× (increment valueUtils c₀) (increment valueUtils c₁)
          valueUtils .increment (list𝒞 c) = incrementList (increment valueUtils c)
          valueUtils .increment nat𝒞 = incrementNat
          valueUtils .increment string𝒞 = incrementString
          valueUtils .apply bool𝒞 bool𝒞 = applyBool
          valueUtils .apply fd𝒞 fd𝒞 = applyFD
          valueUtils .apply (⊎𝒞 c₀ c₁) (⊎𝒞 c₂ c₃) = apply⊎ c₀ c₁ c₂ c₃ (apply valueUtils (⊎𝒞 c₀ c₁) c₂) (apply valueUtils (⊎𝒞 c₀ c₁) c₃)
          valueUtils .apply (×𝒞 c₀ c₁) (×𝒞 c₂ c₃) = apply× c₀ c₁ c₂ c₃ (apply valueUtils (×𝒞 c₀ c₁) c₂) (apply valueUtils (×𝒞 c₀ c₁) c₃)
          valueUtils .apply (list𝒞 c₀) (list𝒞 c₁) = applyList c₀ c₁ (apply valueUtils (list𝒞 c₀) c₁)
          valueUtils .apply nat𝒞 nat𝒞 = applyNat
          valueUtils .apply string𝒞 string𝒞 = applyString
          valueUtils .apply i₀ bool𝒞 n subst expr = expr
          valueUtils .apply i₀ fd𝒞 n subst expr = expr
          valueUtils .apply i₀ nat𝒞 n subst expr = expr
          valueUtils .apply i₀ string𝒞 n subst expr = expr
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
          solver .solve bool𝒞 = unifyDisunify bool𝒞 ⦃ decMy𝒞 ⦄ ⦃ ftUtilsBool ⦄ ⦃ valueUtils ⦄ ⦃ ftUtils⊥ ⦄ ⦃ constraintUtils ⦄ ⦃ decBool ⦄ ⦃ makeVarBool ⦄ ⦃ showBool ⦄ ⦃ mapShowConstraint bool𝒞 ⦄
          solver .solve fd𝒞 _ _ constraints new y = 
            (Data.List.map (λ x → (x , y)) ∘ Data.List.map (Data.List.map 
              (λ {(inj₁ x) → inj₁ (generalize fd𝒞 ⦃ ftUtilsFD ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ decFD ⦄ x) ; 
                  (inj₂ x) → inj₂ (generalizeCustom fd𝒞 ⦃ ftUtilsFD ⦄ ⦃ ftUtilsℒFD ⦄ ⦃ decFD ⦄ x)})) ∘ fdSolve) (new ++ constraints)
          solver .solve (⊎𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify (⊎𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ mapDecEq (⊎𝒞 c₀ c₁) ⦄ ⦃ mapMakeVar (⊎𝒞 c₀ c₁) ⦄ ⦃ mapShow (⊎𝒞 c₀ c₁) ⦄ ⦃ mapShowConstraint (⊎𝒞 c₀ c₁) ⦄
          solver .solve (×𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify (×𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ mapDecEq (×𝒞 c₀ c₁) ⦄ ⦃ mapMakeVar (×𝒞 c₀ c₁) ⦄ ⦃ mapShow (×𝒞 c₀ c₁) ⦄ ⦃ mapShowConstraint (×𝒞 c₀ c₁) ⦄
          solver .solve (list𝒞 c) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify (list𝒞 c) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ mapDecEq (list𝒞 c) ⦄ ⦃ mapMakeVar (list𝒞 c) ⦄ ⦃ mapShow (list𝒞 c) ⦄ ⦃ mapShowConstraint (list𝒞 c) ⦄
          solver .solve nat𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify nat𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ mapDecEq nat𝒞 ⦄ ⦃ mapMakeVar nat𝒞 ⦄ ⦃ mapShow nat𝒞 ⦄ ⦃ mapShowConstraint nat𝒞 ⦄
          solver .solve string𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = unifyDisunify string𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ mapDecEq string𝒞 ⦄ ⦃ mapMakeVar string𝒞 ⦄ ⦃ mapShow string𝒞 ⦄ ⦃ mapShowConstraint string𝒞 ⦄

-- Here, for every domain a grounder can be added. This only returns some ground variable assignments for which the constraints hold
instance  grounder : Grounder My𝒞 ⟦_⟧ ⟦_⟧ℒ
          grounder .ground bool𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = groundImpl bool𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄
          grounder .ground fd𝒞 = labeling
          grounder .ground (⊎𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = groundImpl (⊎𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ dec⊎ ⦃ mapDecEq c₀ ⦄ ⦃ mapDecEq c₁ ⦄ ⦄ ⦃ mapMakeVar (⊎𝒞 c₀ c₁) ⦄ ⦃ mapShow (⊎𝒞 c₀ c₁) ⦄ ⦃ mapShowConstraint (⊎𝒞 c₀ c₁) ⦄
          grounder .ground (×𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = groundImpl (×𝒞 c₀ c₁) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ dec× ⦃ mapDecEq c₀ ⦄ ⦃ mapDecEq c₁ ⦄ ⦄ ⦃ mapMakeVar (×𝒞 c₀ c₁) ⦄ ⦃ mapShow (×𝒞 c₀ c₁) ⦄ ⦃ mapShowConstraint (×𝒞 c₀ c₁) ⦄
          grounder .ground (list𝒞 c) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = groundImpl (list𝒞 c) ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ decList ⦃ mapDecEq c ⦄ ⦄ ⦃ mapMakeVar (list𝒞 c) ⦄ ⦃ mapShow (list𝒞 c) ⦄ ⦃ mapShowConstraint (list𝒞 c) ⦄
          grounder .ground nat𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = groundImpl nat𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ decNat ⦄ ⦃ mapMakeVar nat𝒞 ⦄ ⦃ mapShow nat𝒞 ⦄ ⦃ mapShowConstraint nat𝒞 ⦄
          grounder .ground string𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ = groundImpl string𝒞 ⦃ a ⦄ ⦃ b ⦄ ⦃ d ⦄ ⦃ e ⦄ ⦃ f ⦄ ⦃ decString ⦄ ⦃ mapMakeVar string𝒞 ⦄ ⦃ mapShow string𝒞 ⦄ ⦃ mapShowConstraint string𝒞 ⦄

-- It is not recommended to modify the scheduler, defaultSchedule is perfectly safe and usable for any domain group.
instance  scheduler : Scheduler My𝒞 ⟦_⟧ ⟦_⟧ℒ
          scheduler .schedule = defaultSchedule ⦃ decMy𝒞 ⦄ ⦃ valueUtils ⦄ ⦃ constraintUtils ⦄ ⦃ solver ⦄