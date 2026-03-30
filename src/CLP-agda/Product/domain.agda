module Product.domain where

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Show
open import Data.Maybe
open import Data.List
open import Function.Base

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics
open import CLP.ftUtilsDerivation
open import CLP.types

data ×Logic (A : Set) (B : Set) : Set where
  _∶_ : A → B → ×Logic A B
  var× : ℕ → ×Logic A B

×D : HasDesc ×Logic
×D = deriveDesc ×Logic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  decℕ : DecEq ℕ
          decℕ = deriveDecEq ℕD

instance  showℕ : Show ℕ
          showℕ .Generics.show = Data.Nat.Show.show

instance  makeVar× : ∀ {A B} → MakeVar (×Logic A B)
          makeVar× .fresh = var×
          makeVar× .new = var× 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  ftUtils× : ∀ {A B} → ⦃ FTUtils A ⦄ → ⦃ FTUtils B ⦄ → FTUtils (×Logic A B)
          ftUtils× = deriveFTUtils ×D

fold× = deriveFold ×D

instance  dec× : ∀ {A B} → ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (×Logic A B)
          dec× = deriveDecEq ×D

instance  show× : ∀ {A B} → ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (×Logic A B)
          show× = deriveShow ×D

apply× : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → ⦃ DecEq 𝒞 ⦄
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → (c₂ : 𝒞)
  → (c₃ : 𝒞)
  → (ℕ → ×Logic (Code c₀) (Code c₁) → Code c₂ → Code c₂)
  → (ℕ → ×Logic (Code c₀) (Code c₁) → Code c₃ → Code c₃)
  → ℕ 
  → ×Logic (Code c₀) (Code c₁) → ×Logic (Code c₂) (Code c₃) → ×Logic (Code c₂) (Code c₃)
apply× c₀ c₁ c₂ c₃ _ _ n subst (var× m) with c₀ ≟ c₂ | c₁ ≟ c₃
... | yes refl | yes refl = if m ≡ᵇ n then subst else (var× m)
... | _ | _ = var× m
apply× c₀ c₁ c₂ c₃ app₀ app₁ n subst (a ∶ b) = (app₀ n subst a) ∶ (app₁ n subst b)

zipMatch× : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → ⦃ FTUtils (Code c₀) ⦄
  → ⦃ FTUtils (Constraint c₀) ⦄
  → ⦃ DecEq (Code c₀) ⦄
  → ⦃ MakeVar (Code c₀) ⦄
  → ⦃ Show (Code c₀) ⦄
  → ⦃ Show (Constraint c₀) ⦄
  → ⦃ FTUtils (Code c₁) ⦄
  → ⦃ FTUtils (Constraint c₁) ⦄
  → ⦃ DecEq (Code c₁) ⦄
  → ⦃ MakeVar (Code c₁) ⦄
  → ⦃ Show (Code c₁) ⦄
  → ⦃ Show (Constraint c₁) ⦄
  → ×Logic (Code c₀) (Code c₁)
  → ×Logic (Code c₀) (Code c₁)
  → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint))
zipMatch× c₀ c₁ (a ∶ b) (x ∶ y) = just ((_:-:_ c₀ (a =ℒ x)) ∷ (_:-:_ c₁ (b =ℒ y)) ∷ [])
zipMatch× _ _ _ _ = nothing

increment× : ∀ {A B} → (ℕ → A → A) → (ℕ → B → B) → ℕ → ×Logic A B → ×Logic A B
increment× inc₀ inc₁ x = fold× (λ a b → inc₀ x a ∶ inc₁ x b) (λ y → var× (x + y))