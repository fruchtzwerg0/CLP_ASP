module Term.utilities where

open import Term.ftUtilsDerivation
open import Term.types
open import Data.Bool hiding (_≟_)
open import Data.Nat 
  using (ℕ; _≡ᵇ_; _⊓_; _+_)
open import Data.List 
  using (List; []; _∷_; map; any; all; _++_)
open import Data.Maybe 
  using (Maybe; just; nothing)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality
open import Generics
open import Function.Base


-- generic apply function applyᵥ extended by term.

applyConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Code : (𝒞 → Set))
  → ℕ 
  → ⦃ FTUtils (Code c) ⦄ 
  → Code c
  → (ℒ ∘ Code) c
  → (ℒ ∘ Code) c
applyConstraint C c code k te (x =ℒ y) = apply k te x =ℒ apply k te y
applyConstraint C c code k te (x ≠ℒ y) = apply k te x ≠ℒ apply k te y

applyCustomConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Constraint : (𝒞 → Set))
  → ℕ 
  → ⦃ FTUtils (Constraint c) ⦄ 
  → Constraint c
  → (Dual ∘ Constraint) c
  → (Dual ∘ Constraint) c
applyCustomConstraint C c cns k te (default cust) = (default ∘ apply k te) cust
applyCustomConstraint C c cns k te (dual cust) = (dual ∘ apply k te) cust
{-
{-# TERMINATING #-}
applyᵥ : 
  {hv : HasVariables}
  → (𝒞 : Set)
  → (c : 𝒞)
  → (Code : (𝒞 → Set))
  → (Constraint : (𝒞 → Set))
  → (Atom : Set)
  → ⦃ FTUtils Atom ⦄
  → ℕ
  → Code c
  → ⟦ 𝒞 , Code , Constraint , Atom , hv ⟧ᵥ
  → ⟦ 𝒞 , Code , Constraint , Atom , hv ⟧ᵥ

applyᵥ {domainExpr} C c code cns at = apply

--applyᵥ {mixedConstraint} C c code cns at k te (inj₁ (c₁ , l)) = (inj₁ (c₁ , applyConstraint C c₁ code k te l))
--applyᵥ {mixedConstraint} C c code cns at k te (inj₂ (c₁ , l)) = (inj₂ (c₁ , applyCustomConstraint C c₁ cns k te l))

--applyᵥ {atom} C c code cns at = apply

applyᵥ {literal} C c code cns at k te (atom a) = atom (applyᵥ {atom} C c code cns at k te a)
applyᵥ {literal} C c code cns at k te (constraint ℓ)    = constraint (applyᵥ {mixedConstraint} C c code cns at k te ℓ)

applyᵥ {clause} C c code cns at k te (head :-- body) =
  applyᵥ {atom} C c code cns at k te head :-- Data.List.map (applyᵥ {literal} C c code cns at k te) body

applyᵥ {listOf y} C c code cns at k te xs =
  Data.List.map (applyᵥ {y} C c code cns at k te) xs
-}
-- generic occurs function occursᵥ extended by term.

occursConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Code : (𝒞 → Set))
  → ℕ 
  → ⦃ FTUtils (Code c) ⦄ 
  → (ℒ ∘ Code) c
  → Bool
occursConstraint C c code k (x =ℒ y) = occurs k x ∨ occurs k y
occursConstraint C c code k (x ≠ℒ y) = occurs k x ∨ occurs k y

occursCustomConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Constraint : (𝒞 → Set))
  → ℕ 
  → ⦃ FTUtils (Constraint c) ⦄ 
  → (Dual ∘ Constraint) c
  → Bool
occursCustomConstraint C c code k (default cust) = occurs k cust
occursCustomConstraint C c code k (dual cust) = occurs k cust

{-# TERMINATING #-}
occursᵥ : 
  {hv : HasVariables}
  → {Atom : Set}
  → (𝒞 : Set)
  → (Code : (𝒞 → Set))
  → (Constraint : (𝒞 → Set))
  → ℕ
  → ⟦ 𝒞 , Code , Constraint , Atom , hv ⟧ᵥ
  → Bool

occursᵥ {domainExpr} C code cns k (_ :-: l) = occurs k l

occursᵥ {mixedConstraint} C code cns k (inj₁ (c₁ :-: l)) = occursConstraint C c₁ code k l
occursᵥ {mixedConstraint} C code cns k (inj₂ (c₁ :-: l)) = occursCustomConstraint C c₁ cns k l

occursᵥ {domainConstraint} C code cns k (c₁ :-: l) = occursCustomConstraint C c₁ cns k l
occursᵥ {genericConstraint} C code cns k (c₁ :-: l) = occursConstraint C c₁ code k l

occursᵥ {atom} C code cns k (_<ᵢ x ⦃ inst ⦄) = occurs k x

occursᵥ {literal} C code cns k (atom a) = occursᵥ {atom} C code cns k (_<ᵢ a)
occursᵥ {literal} {at} C code cns k (constraint ℓ) = occursᵥ {mixedConstraint} {at} C code cns k ℓ

occursᵥ {clause} C code cns k (head :-- body) =
  occursᵥ {atom} C code cns k (_<ᵢ head) ∨ any (occursᵥ {literal} C code cns k) body

occursᵥ {listOf y} C code cns k xs =
  any (occursᵥ {y} C code cns k) xs

-- generic increment function incrementᵥ extended by term.

incrementConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Code : (𝒞 → Set))
  → ℕ 
  → ⦃ FTUtils (Code c) ⦄ 
  → (ℒ ∘ Code) c
  → (ℒ ∘ Code) c
incrementConstraint C c code k (x =ℒ y) = increment k x =ℒ increment k y
incrementConstraint C c code k (x ≠ℒ y) = increment k x ≠ℒ increment k y

incrementCustomConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Constraint : (𝒞 → Set))
  → ℕ 
  → ⦃ FTUtils (Constraint c) ⦄ 
  → (Dual ∘ Constraint) c
  → (Dual ∘ Constraint) c
incrementCustomConstraint C c code k (default cust) = (default ∘ increment k) cust
incrementCustomConstraint C c code k (dual cust) = (dual ∘ increment k) cust

{-# TERMINATING #-}
incrementᵥ : 
  {hv : HasVariables}
  → (𝒞 : Set)
  → (Code : (𝒞 → Set))
  → (Constraint : (𝒞 → Set))
  → (Atom : Set) 
  → ℕ 
  → ⟦ 𝒞 , Code , Constraint , Atom , hv ⟧ᵥ 
  → ⟦ 𝒞 , Code , Constraint , Atom , hv ⟧ᵥ

incrementᵥ {domainExpr} C code cns at k (c₁ :-: l) = (c₁ :-: increment k l)

incrementᵥ {mixedConstraint} C code cns at k (inj₁ (c₁ :-: l)) = (inj₁ (c₁ :-: incrementConstraint C c₁ code k l))
incrementᵥ {mixedConstraint} C code cns at k (inj₂ (c₁ :-: l)) = (inj₂ (c₁ :-: incrementCustomConstraint C c₁ cns k l))

incrementᵥ {domainConstraint} C code cns at k (c₁ :-: l) = c₁ :-: incrementCustomConstraint C c₁ cns k l
incrementᵥ {genericConstraint} C code cns at k (c₁ :-: l) = c₁ :-: incrementConstraint C c₁ code k l

incrementᵥ {atom} C code cns at k (_<ᵢ x ⦃ inst ⦄) = _<ᵢ (increment k x) ⦃ inst ⦄

incrementᵥ {literal} C code cns at k (atom a ⦃ inst ⦄) with incrementᵥ {atom} C code cns at k (_<ᵢ a ⦃ inst ⦄)
incrementᵥ {literal} C code cns at k (atom a ⦃ inst ⦄) | _<ᵢ res = atom res ⦃ inst ⦄
incrementᵥ {literal} C code cns at k (constraint ℓ) = constraint (incrementᵥ {mixedConstraint} C code cns at k ℓ)

incrementᵥ {clause} C code cns at k (_:--_ head body ⦃ inst ⦄) with incrementᵥ {atom} C code cns at k (_<ᵢ head ⦃ inst ⦄)
incrementᵥ {clause} C code cns at k (_:--_ head body ⦃ inst ⦄) | _<ᵢ res = 
  _:--_ res (Data.List.map (incrementᵥ {literal} C code cns at k) body) ⦃ inst ⦄

incrementᵥ {listOf y} C code cns at k xs =
  Data.List.map (incrementᵥ {y} C code cns at k) xs

collectVarsConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Code : (𝒞 → Set))
  → ⦃ FTUtils (Code c) ⦄ 
  → (ℒ ∘ Code) c
  → List ℕ
collectVarsConstraint C c code (x =ℒ y) = collectVars x ++ collectVars y
collectVarsConstraint C c code (x ≠ℒ y) = collectVars x ++ collectVars y

collectVarsCustomConstraint : 
  (𝒞 : Set)
  → (c : 𝒞)
  → (Constraint : (𝒞 → Set))
  → ⦃ FTUtils (Constraint c) ⦄ 
  → (Dual ∘ Constraint) c
  → List ℕ
collectVarsCustomConstraint C c code (default cust) = collectVars cust
collectVarsCustomConstraint C c code (dual cust) = collectVars cust

{-# TERMINATING #-}
collectVarsᵥ : 
  {hv : HasVariables}
  → {Atom : Set}
  → (𝒞 : Set)
  → (Code : (𝒞 → Set))
  → (Constraint : (𝒞 → Set))
  → ⟦ 𝒞 , Code , Constraint , Atom , hv ⟧ᵥ 
  → List ℕ

collectVarsᵥ {domainExpr} C code cns (_ :-: l) = collectVars l

collectVarsᵥ {mixedConstraint} C code cns (inj₁ (c₁ :-: l)) = collectVarsConstraint C c₁ code l
collectVarsᵥ {mixedConstraint} C code cns (inj₂ (c₁ :-: l)) = collectVarsCustomConstraint C c₁ cns l

collectVarsᵥ {domainConstraint} C code cns (c₁ :-: l) = collectVarsCustomConstraint C c₁ cns l
collectVarsᵥ {genericConstraint} C code cns (c₁ :-: l) = collectVarsConstraint C c₁ code l

collectVarsᵥ {atom} C code cns (_<ᵢ x ⦃ inst ⦄)  = collectVars x

collectVarsᵥ {literal} C code cns (atom a ⦃ inst ⦄) = collectVarsᵥ {atom} C code cns (_<ᵢ a ⦃ inst ⦄)
collectVarsᵥ {literal} {at} C code cns (constraint ℓ) = collectVarsᵥ {mixedConstraint} {at} C code cns ℓ

collectVarsᵥ {clause} C code cns (_:--_ head body ⦃ inst ⦄) =
  collectVarsᵥ {atom} C code cns (_<ᵢ head ⦃ inst ⦄) ++ collectVarsᵥ {listOf literal} C code cns body

collectVarsᵥ {listOf _} C code cns []       = []
collectVarsᵥ {listOf y} C code cns (x ∷ xs) = collectVarsᵥ {y} C code cns x ++ collectVarsᵥ {listOf y} C code cns xs

getPermission :
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → (c : 𝒞)
  → Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint
  → Maybe ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
getPermission x (inj₁ (b :-: a)) with x ≟ b
... | no _ = nothing
... | (yes refl) = just (inj₁ a)
getPermission x (inj₂ (b :-: a)) with x ≟ b
... | no _ = nothing
... | (yes refl) = just (inj₂ a)

getElse :
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → (c : 𝒞)
  → Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint
  → Maybe (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
getElse x (inj₁ (b :-: a)) with x ≟ b
... | no _ = just (inj₁ (b :-: a))
... | (yes refl) = nothing
getElse x (inj₂ (b :-: a)) with x ≟ b
... | no _ = just (inj₂ (b :-: a))
... | (yes refl) = nothing

generalize : ∀ {𝒞 Code Constraint}
 → (c : 𝒞)
 → ⦃ FTUtils (Code c) ⦄ 
 → ⦃ FTUtils (Constraint c) ⦄ 
 → (ℒ ∘ Code) c 
 → Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
generalize c p  = _:-:_ c p