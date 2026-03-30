module List.domain where

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Show
open import Data.Maybe
open import Data.List
open import Data.Product
open import Function.Base

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics
open import CLP.ftUtilsDerivation
open import CLP.types

data ListLogic (A : Set) : Set where
  []  : ListLogic A
  _∷_ : A → ListLogic A → ListLogic A
  varList : ℕ → ListLogic A

listD : HasDesc ListLogic
listD = deriveDesc ListLogic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  decℕ : DecEq ℕ
          decℕ = deriveDecEq ℕD

instance  showℕ : Show ℕ
          showℕ .Generics.show = Data.Nat.Show.show

instance  makeVarList : ∀ {A} → MakeVar (ListLogic A)
          makeVarList .fresh = varList
          makeVarList .new = varList 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  ftUtilsList : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ListLogic A)
          ftUtilsList = deriveFTUtils listD

foldList = deriveFold listD

instance  decList : ∀ {A} → ⦃ DecEq A ⦄ → DecEq (ListLogic A)
          decList = deriveDecEq listD

instance  showList : ∀ {A} → ⦃ Show A ⦄ → Show (ListLogic A)
          showList = deriveShow listD

applyList : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
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
applyList c₀ c₁ app n subst (x ∷ xs) = app n subst x ∷ applyList c₀ c₁ app n subst xs

zipMatchList : 
  {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → (c : 𝒞)
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → ListLogic (Code c)
  → ListLogic (Code c)
  → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℒ (ListLogic (Code c))))
zipMatchList c (a ∷ b) (x ∷ y) = just ((_:-:_ c (a =ℒ x)) ∷ [] , (b =ℒ y) ∷ [])
zipMatchList _ [] [] = just ([] , [])
zipMatchList _ _ _ = nothing

incrementList : ∀ {A} → (ℕ → A → A) → ℕ → ListLogic A → ListLogic A
incrementList inc x = foldList [] (λ a b → inc x a ∷ b) (λ y → varList (x + y))