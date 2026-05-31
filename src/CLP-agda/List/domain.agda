module List.domain where

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Show
open import Data.Maybe
open import Data.List hiding (_++_)
open import Data.String hiding (_≟_)
open import Data.Product
open import Function.Base
open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality
open import Generics
open import CLP.ftUtilsDerivation
open import CLP.types

data ListLogic (A : Set) : Set where
  []      : ListLogic A
  _∷_     : A → ListLogic A → ListLogic A
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
          makeVarList .new   = varList 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

-- ----------------------------------------------------------------
-- Manual FTUtils for ListLogic.
--
-- Parameterized in A via instance arg.  The cons case
-- conjuncts/concatenates element FTUtils with recursive call on
-- the tail.  varList returns its index.
-- ----------------------------------------------------------------
instance ftUtilsList :
           ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (ListLogic A)

         ftUtilsList .functor []          = "[]"
         ftUtilsList .functor (_ ∷ _)     = "∷"
         ftUtilsList .functor (varList _) = "varList"

         ftUtilsList .varName (varList n) = just n
         ftUtilsList .varName _           = nothing

         ftUtilsList              .occurs _ []          = false
         ftUtilsList ⦃ fA ⦄       .occurs n (a ∷ as)    = occurs ⦃ fA ⦄ n a ∨ occurs ⦃ ftUtilsList ⦃ fA ⦄ ⦄ n as
         ftUtilsList              .occurs n (varList m) = n ≡ᵇ m

         ftUtilsList              .collectVars []          = []
         ftUtilsList ⦃ fA ⦄       .collectVars (a ∷ as)    = collectVars ⦃ fA ⦄ a Data.List.++ collectVars ⦃ ftUtilsList ⦃ fA ⦄ ⦄ as
         ftUtilsList              .collectVars (varList n) = n ∷ []

         ftUtilsList .getNat _ = nothing

-- ----------------------------------------------------------------
-- Manual fold for ListLogic.
-- ----------------------------------------------------------------
foldList :
  ∀ {A B : Set}
  → B                  -- []
  → (A → B → B)        -- ∷
  → (ℕ → B)            -- varList
  → ListLogic A → B
foldList fn fc fv []          = fn
foldList fn fc fv (a ∷ as)    = fc a (foldList fn fc fv as)
foldList fn fc fv (varList n) = fv n

instance  decList : ∀ {A} → ⦃ DecEq A ⦄ → DecEq (ListLogic A)
          decList = deriveDecEq listD

instance  showList : ∀ {A} → ⦃ Show A ⦄ → Show (ListLogic A)
          showList ⦃ sh ⦄ .Generics.show (x ∷ xs) = "(" ++ Generics.show x ++ " :: " ++ Generics.show xs ++ ")"
          showList .Generics.show [] = "[]"
          showList .Generics.show (varList x) = "varList " ++ Data.Nat.Show.show x

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

-- Direct (non-fold) implementation of incrementList.
{-# TERMINATING #-}
incrementList : ∀ {A} → (ℕ → A → A) → ℕ → ListLogic A → ListLogic A
incrementList inc x []          = []
incrementList inc x (a ∷ as)    = inc x a ∷ incrementList inc x as
incrementList inc x (varList n) = varList (x + n)