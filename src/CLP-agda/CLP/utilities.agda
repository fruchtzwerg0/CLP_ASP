module CLP.utilities where

open import CLP.ftUtilsDerivation
open import CLP.types
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

applyConstraint : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄ 
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → ℕ 
  → Code c₀
  → (ℒ ∘ Code) c₁
  → (ℒ ∘ Code) c₁
applyConstraint ⦃ ft ⦄ c₀ c₁ k sub (x =ℒ y) = apply ft c₀ c₁ k sub x =ℒ apply ft c₀ c₁ k sub y
applyConstraint ⦃ ft ⦄ c₀ c₁ k sub (x ≠ℒ y) = apply ft c₀ c₁ k sub x ≠ℒ apply ft c₀ c₁ k sub y

applyCustomConstraint : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄ 
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → ℕ 
  → Code c₀
  → (Dual ∘ Constraint) c₁
  → (Dual ∘ Constraint) c₁
applyCustomConstraint ⦃ ft ⦄ c₀ c₁ k sub (default cust) = default (apply ft c₀ c₁ k sub cust)
applyCustomConstraint ⦃ ft ⦄ c₀ c₁ k sub (dual cust) = dual (apply ft c₀ c₁ k sub cust)

applyMixedConstraint : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄ 
  → (c : 𝒞)
  → ℕ 
  → Code c
  → Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint
  → Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint
applyMixedConstraint ⦃ ft ⦄ c k sub (inj₁ (c₁ :-: l)) = (inj₁ (c₁ :-: applyConstraint ⦃ ft ⦄ c c₁ k sub l))
applyMixedConstraint ⦃ _ ⦄ ⦃ ft ⦄ c k sub (inj₂ (c₁ :-: l)) = (inj₂ (c₁ :-: applyCustomConstraint ⦃ ft ⦄ c c₁ k sub l))

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

incrementCustomConstraint : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄ 
  → (c : 𝒞)
  → ℕ 
  → (Dual ∘ Constraint) c
  → (Dual ∘ Constraint) c
incrementCustomConstraint ⦃ ft ⦄ c k (default cust) = (default ∘ increment ft c k) cust
incrementCustomConstraint ⦃ ft ⦄ c k (dual cust) = (dual ∘ increment ft c k) cust

incrementConstraint : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄ 
  → (c : 𝒞)
  → ℕ 
  → (ℒ ∘ Code) c
  → (ℒ ∘ Code) c
incrementConstraint ⦃ ft ⦄ c k (x =ℒ y) = increment ft c k x =ℒ increment ft c k y
incrementConstraint ⦃ ft ⦄ c k (x ≠ℒ y) = increment ft c k x ≠ℒ increment ft c k y

incrementLiteral : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ℕ
  → Literal Atom 𝒞 Code Constraint
  → Literal Atom 𝒞 Code Constraint
incrementLiteral n (atom ⦃ _ ⦄ ⦃ fs ⦄ x) = atom (increment fs n x)
incrementLiteral n (constraint (inj₁ (_:-:_ c l))) = constraint (inj₁ (c :-: incrementConstraint c n l))
incrementLiteral n (constraint (inj₂ (_:-:_ c l))) = constraint (inj₂ (c :-: incrementCustomConstraint c n l))

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

collectVarsᵥ {literal} C code cns (atom ⦃ inst ⦄ a) = collectVarsᵥ {atom} C code cns (_<ᵢ a ⦃ inst ⦄)
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
 → ⦃ DecEq (Code c) ⦄
 → ⦃ MakeVar (Code c) ⦄
 → ⦃ Show (Code c) ⦄
 → ⦃ Show (Constraint c) ⦄
 → (ℒ ∘ Code) c 
 → Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint
generalize c p  = _:-:_ c p

generalizeCustom : ∀ {𝒞 Code Constraint}
 → (c : 𝒞)
 → ⦃ FTUtils (Code c) ⦄
 → ⦃ FTUtils (Constraint c) ⦄ 
 → ⦃ DecEq (Code c) ⦄
 → ⦃ MakeVar (Code c) ⦄
 → ⦃ Show (Code c) ⦄
 → ⦃ Show (Constraint c) ⦄
 → (Dual ∘ Constraint) c 
 → Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint
generalizeCustom c p  = _:-:_ c p

generalizeEqual : ∀ {𝒞 Code Constraint}
 → (c : 𝒞)
 → ⦃ FTUtils (Code c) ⦄
 → ⦃ FTUtils (Constraint c) ⦄ 
 → ⦃ DecEq (Code c) ⦄
 → ⦃ MakeVar (Code c) ⦄
 → ⦃ Show (Code c) ⦄
 → ⦃ Show (Constraint c) ⦄
 → (ℕ × Code c) 
 → Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint
generalizeEqual c p  = _:-:_ c p

generalizeDisequal : ∀ {𝒞 Code Constraint}
 → (c : 𝒞)
 → ⦃ FTUtils (Code c) ⦄
 → ⦃ FTUtils (Constraint c) ⦄ 
 → ⦃ DecEq (Code c) ⦄
 → ⦃ MakeVar (Code c) ⦄
 → ⦃ Show (Code c) ⦄
 → ⦃ Show (Constraint c) ⦄
 → ℕ × Code c
 → Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint
generalizeDisequal c p  = _:-:_ c p

generalizeGround : 
  ∀ {𝒞 Code Constraint}
  → (c : 𝒞)
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (ℕ × Code c) ⊎ (ℕ × Code c)
  → (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint)
generalizeGround c (inj₁ x) = (inj₁ ∘ generalizeEqual c) x
generalizeGround c (inj₂ x) = (inj₂ ∘ generalizeDisequal c) x