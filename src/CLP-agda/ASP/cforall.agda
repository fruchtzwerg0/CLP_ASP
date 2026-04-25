module ASP.cforall where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Data.Bool hiding (_≟_)
open import Data.String 
  using (String; _==_)
open import Data.Nat hiding (equal; _≟_)
open import Data.List
open import Data.List.Base
open import Data.List.Membership.DecSetoid using (_∈?_)
open import Data.Maybe 
  using (Maybe; just; nothing; map; is-just)
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Function.Base

open import Generics

open import CLP.clp
open import ASP.dual

cForall₀ : 
  ∀ {𝒞 Code Constraint}
  → {Custom : Set}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ℕ
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → (Maybe ∘ List) (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
cForall₀ _ [] _ = just []
cForall₀ {C}{Code}{Constraint} v (an@(_ , answer) ∷ answers) store = 
  let
    -- For each answer branch, split into V-mentioning and non-V constraints
    xy : List (List _ × List _)
    xy = Data.List.map (partitionᵇ (any (_≡ᵇ_ v) ∘ collectVarsᵥ {_}{⊤} C Code Constraint)) answer
    
    -- The V-constraints per branch (the A_V projection)
    vConstraints : List (List _)
    vConstraints = Data.List.map proj₁ xy

    -- The non-V constraints per branch get added to every store branch
    nonVPerBranch : List (List _)
    nonVPerBranch = Data.List.map proj₂ xy
    
    -- Merge non-V constraints into the accumulated store
    storeWithNonV : List (List _)
    storeWithNonV = concat (Data.List.map (λ s → Data.List.map (λ nv → s ++ nv) nonVPerBranch) store)
    
    -- For each answer branch: test if the negation of its V-constraints,
    -- conjoined with storeWithNonV, is satisfiable.
    -- Negation of a conjunction is a disjunction: ¬(c1 ∧ c2 ∧ ...) = ¬c1 ∨ ¬c2 ∨ ...
    -- For each disjunct ¬ci: schedule (¬ci ∷ []) against storeWithNonV.
    -- The answer "covers" storeWithNonV iff NONE of the disjuncts is satisfiable
    -- (i.e., all attempts to find a model in the complement fail).
    --
    -- Per branch: 
    --   branchCovers = all (λ cn → null (schedule (negate cn ∷ []) storeWithNonV)) vCns
    -- If branchCovers is true → A_V is equivalent to or stronger than the store,
    --   and we can continue with remaining answers on the same store.
    -- If branchCovers is false → the answer doesn't cover; compute the refinement
    --   by conjoining storeWithNonV with each ¬ci (a list of new stores), 
    --   and recurse on the remaining answers with that new store.
    
    branchCovers : List _ → Bool
    branchCovers vCns = all 
      (λ cn → null (schedule (negateConstraint cn ∷ []) storeWithNonV)) 
      vCns
    
    -- For a non-covering branch, compute the refined stores: one per disjunct
    -- whose conjunction with storeWithNonV is satisfiable.
    refineStores : List _ → List (List _)
    refineStores vCns = concat (Data.List.map 
      (λ cn → filterᵇ (Data.Bool.not ∘ null) (schedule (negateConstraint cn ∷ []) storeWithNonV)) 
      vCns)
    
    -- Process each answer branch
    covers : Bool
    covers = any branchCovers vConstraints
    
    refinement : List (List _)
    refinement = concat (Data.List.map refineStores vConstraints)
  in
  if covers 
  then cForall₀ v answers store Data.Maybe.>>= (just ∘ (_∷_ an))
  else 
    if null refinement
    then nothing  -- c-forall fails: answer neither covers nor refines
    else cForall₀ v answers refinement Data.Maybe.>>= (just ∘ (_∷_ an))
    
cForall : 
  ∀ {𝒞 Code Constraint}
  → {Custom : Set}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ℕ
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
  → (Maybe ∘ List) (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
cForall v answers = cForall₀ v answers ([] ∷ [])