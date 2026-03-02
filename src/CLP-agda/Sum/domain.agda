module Sum.domain where

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Maybe
open import Data.List
open import Function.Base

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics
open import Term.ftUtilsDerivation
open import Term.types

data ⊎Logic (A : Set) (B : Set) : Set where
  p : A → ⊎Logic A B
  q : B → ⊎Logic A B
  var⊎ : ℕ → ⊎Logic A B

⊎D : HasDesc ⊎Logic
⊎D = deriveDesc ⊎Logic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  makeVar⊎ : ∀ {A B} → MakeVar (⊎Logic A B)
          makeVar⊎ .fresh = var⊎
          makeVar⊎ .new = var⊎ 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  unifyDisunify⊎ : ∀ {A B} → ⦃ FTUtils A ⦄ → ⦃ FTUtils B ⦄ → FTUtils (⊎Logic A B)
          unifyDisunify⊎ = deriveFTUtils ⊎D

fold⊎ = deriveFold ⊎D

apply⊎ : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ DecEq 𝒞 ⦄
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → (ℕ → ⊎Logic (Code c₀) (Code c₁) → Code c₀ → Code c₀)
  → (ℕ → ⊎Logic (Code c₀) (Code c₁) → Code c₁ → Code c₁)
  → ℕ 
  → ⊎Logic (Code c₀) (Code c₁) → ⊎Logic (Code c₀) (Code c₁) → ⊎Logic (Code c₀) (Code c₁)
apply⊎ c₀ c₁ _ _ n subst (var⊎ m) with c₀ ≟ c₁
... | yes refl = if m ≡ᵇ n then subst else (var⊎ m)
... | no _ = var⊎ m
apply⊎ {C}{Code}{Constraint} c₀ c₁ app₀ app₁ n subst (p expr) = p (app₀ n subst expr)
apply⊎ {C}{Code}{Constraint} c₀ c₁ app₀ app₁ n subst (q expr) = q (app₁ n subst expr)

zipMatch⊎ : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → ⦃ FTUtils (Code c₀) ⦄
  → ⦃ FTUtils (Constraint c₀) ⦄
  → ⦃ FTUtils (Code c₁) ⦄
  → ⦃ FTUtils (Constraint c₁) ⦄
  → ⊎Logic (Code c₀) (Code c₁)
  → ⊎Logic (Code c₀) (Code c₁)
  → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint))
zipMatch⊎ c₀ c₁ (p x) (p y) = just ((_:-:_ c₀ (x =ℒ y)) ∷ [])
zipMatch⊎ c₀ c₁ (q x) (q y) = just ((_:-:_ c₁ (x =ℒ y)) ∷ [])
zipMatch⊎ _ _ _ _ = nothing

incrementFD : ∀ {A B} → ℕ → ⊎Logic A B → ⊎Logic A B
incrementFD x = fold⊎ p q (λ y → var⊎ (x + y))