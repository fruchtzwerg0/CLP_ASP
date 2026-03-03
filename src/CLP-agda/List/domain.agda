module List.domain where

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

data ListLogic (A : Set) : Set where
  []  : ListLogic A
  _∷_ : A → ListLogic A → ListLogic A
  varList : ℕ → ListLogic A

listD : HasDesc ListLogic
listD = deriveDesc ListLogic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  makeVarList : ∀ {A} → MakeVar (ListLogic A)
          makeVarList .fresh = varList
          makeVarList .new = varList 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  unifyDisunifyList : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ListLogic A)
          unifyDisunifyList = deriveFTUtils listD

foldList = deriveFold listD

applyList : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ DecEq 𝒞 ⦄
  → (c₀ : 𝒞) 
  → (c₁ : 𝒞) 
  → (ℕ → ListLogic (Code c₀) → Code c₁ → Code c₁)
  → ℕ 
  → ListLogic (Code c₀) → ListLogic (Code c₁) → ListLogic (Code c₁)
applyList c₀ c₁ _ n subst (varList m) with c₀ ≟ c₁
... | yes refl = if m ≡ᵇ n then subst else (varList m)
... | no _ = varList m
applyList c₀ c₁ app n subst [] = []
applyList {C}{Code}{Constraint} c₀ c₁ app n subst (x ∷ xs) = app n subst x ∷ applyList {C}{Code}{Constraint} c₀ c₁ app n subst xs
{-
zipMatchList : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → (c₀ : 𝒞)
  → (c₁ : 𝒞)
  → Code c₀ ≡ ListLogic (Code c₁)
  → ListLogic (Code c₁)
  → ListLogic (Code c₁)
  → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint))
zipMatchList c₀ c₁ refl (a ∷ b) (x ∷ y) = just ((_:-:_ c₁ (a =ℒ x)) ∷ (_:-:_ c₀ (b =ℒ y)) ∷ [])
zipMatchList _ _ = nothing
-}
incrementList : ∀ {A} → ℕ → ListLogic A → ListLogic A
incrementList x = foldList [] _∷_ (λ y → varList (x + y))