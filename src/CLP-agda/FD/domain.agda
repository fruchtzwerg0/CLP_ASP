module FD.domain where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.Maybe
open import Data.List hiding (_++_)
open import Data.String hiding (_≟_)
open import Function.Base
open import Agda.Builtin.Int
open import Data.Integer.Show

open import Generics
open import CLP.ftUtilsDerivation
open import CLP.types

data FD : Set where
  ＃_ : Int → FD
  _＃+_ : FD → FD → FD
  _＃-_ : FD → FD → FD
  _＃*_ : FD → FD → FD
  div : FD → FD → FD
  varFD : ℕ → FD

data ℒFD : Set where
  _≤FD_ : FD → FD → ℒFD
  _≥FD_ : FD → FD → ℒFD

infix 100 ＃_
infixr 90 _＃+_
infixr 90 _＃-_
infixr 90 _＃*_

pattern _＃≤_ x y = (default (x ≤FD y))
pattern _＃>_ x y = (dual (x ≤FD y))
pattern _＃≥_ x y = (default (x ≥FD y))
pattern _＃<_ x y = (dual (x ≥FD y))

infixr 80 _＃≤_
infixr 80 _＃>_
infixr 80 _＃≥_
infixr 80 _＃<_

FDD : HasDesc FD
FDD = deriveDesc FD

ℒFDD : HasDesc ℒFD
ℒFDD = deriveDesc ℒFD

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

IntD : HasDesc Int
IntD = deriveDesc Int

instance  decℕ : DecEq ℕ
          decℕ = deriveDecEq ℕD

instance  showℕ : Show ℕ
          showℕ .Generics.show = Data.Nat.Show.show

instance  makeVarFD : MakeVar FD
          makeVarFD .fresh = varFD
          makeVarFD .new = varFD 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  ftUtilsInt : FTUtils Int
          ftUtilsInt .functor _ = "Int"
          ftUtilsInt .getNat _ = nothing
          ftUtilsInt .varName _ = nothing
          ftUtilsInt .occurs _ _ = false
          ftUtilsInt .collectVars _ = []

-- Manual FTUtils for FD.
instance ftUtilsFD : FTUtils FD

         ftUtilsFD .functor (＃ _)    = "Int"
         ftUtilsFD .functor (_ ＃+ _) = "+"
         ftUtilsFD .functor (_ ＃- _) = "-"
         ftUtilsFD .functor (_ ＃* _) = "*"
         ftUtilsFD .functor (div _ _) = "/"
         ftUtilsFD .functor (varFD _) = "varFD"

         ftUtilsFD .varName (varFD n) = just n
         ftUtilsFD .varName _         = nothing

         ftUtilsFD .occurs _ (＃ _)        = false
         ftUtilsFD .occurs n (a ＃+ b)     = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b
         ftUtilsFD .occurs n (a ＃- b)     = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b
         ftUtilsFD .occurs n (a ＃* b)     = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b
         ftUtilsFD .occurs n (div a b)    = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b
         ftUtilsFD .occurs n (varFD m)    = n ≡ᵇ m

         ftUtilsFD .collectVars (＃ _)        = []
         ftUtilsFD .collectVars (a ＃+ b)     = collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b
         ftUtilsFD .collectVars (a ＃- b)     = collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b
         ftUtilsFD .collectVars (a ＃* b)     = collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b
         ftUtilsFD .collectVars (div a b)    = collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b
         ftUtilsFD .collectVars (varFD n)    = n ∷ []

         ftUtilsFD .getNat _ = nothing

-- Manual FTUtils for ℒFD.
instance ftUtilsℒFD : FTUtils ℒFD

         ftUtilsℒFD .functor (_ ≤FD _) = "≤"
         ftUtilsℒFD .functor (_ ≥FD _) = "≥"

         ftUtilsℒFD .varName _ = nothing

         ftUtilsℒFD .occurs n (a ≤FD b) = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b
         ftUtilsℒFD .occurs n (a ≥FD b) = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b

         ftUtilsℒFD .collectVars (a ≤FD b) = collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b
         ftUtilsℒFD .collectVars (a ≥FD b) = collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b

         ftUtilsℒFD .getNat _ = nothing

-- Manual fold for FD.
foldFD :
  ∀ {A : Set}
  → (Int → A)              -- ground int
  → (A → A → A)            -- ＃+
  → (A → A → A)            -- ＃-
  → (A → A → A)            -- ＃*
  → (A → A → A)            -- div
  → (ℕ → A)                -- varFD
  → FD → A
foldFD f₁ f₂ f₃ f₄ f₅ f₆ (＃ i)     = f₁ i
foldFD f₁ f₂ f₃ f₄ f₅ f₆ (a ＃+ b)  = f₂ (foldFD f₁ f₂ f₃ f₄ f₅ f₆ a) (foldFD f₁ f₂ f₃ f₄ f₅ f₆ b)
foldFD f₁ f₂ f₃ f₄ f₅ f₆ (a ＃- b)  = f₃ (foldFD f₁ f₂ f₃ f₄ f₅ f₆ a) (foldFD f₁ f₂ f₃ f₄ f₅ f₆ b)
foldFD f₁ f₂ f₃ f₄ f₅ f₆ (a ＃* b)  = f₄ (foldFD f₁ f₂ f₃ f₄ f₅ f₆ a) (foldFD f₁ f₂ f₃ f₄ f₅ f₆ b)
foldFD f₁ f₂ f₃ f₄ f₅ f₆ (div a b) = f₅ (foldFD f₁ f₂ f₃ f₄ f₅ f₆ a) (foldFD f₁ f₂ f₃ f₄ f₅ f₆ b)
foldFD f₁ f₂ f₃ f₄ f₅ f₆ (varFD n) = f₆ n

instance  decInt : DecEq Int
          decInt = deriveDecEq IntD

instance  showInt : Show Int
          showInt .Generics.show = Data.Integer.Show.show

instance  decFD : DecEq FD
          decFD = deriveDecEq FDD

instance  showFD : Show FD
          showFD .Generics.show (＃ x) = Generics.show x
          showFD .Generics.show (x ＃+ y) = Generics.show x ++ " + " ++ Generics.show y
          showFD .Generics.show (x ＃- y) = Generics.show x ++ " - " ++ Generics.show y
          showFD .Generics.show (x ＃* y) = Generics.show x ++ " * " ++ Generics.show y
          showFD .Generics.show (div x y) = Generics.show x ++ " / " ++ Generics.show y
          showFD .Generics.show (varFD x) = "varFD " ++ Data.Nat.Show.show x

instance  showℒFD : Show ℒFD
          showℒFD .Generics.show (x ≤FD y) = Generics.show x ++ " <= " ++ Generics.show y
          showℒFD .Generics.show (x ≥FD y) = Generics.show x ++ " >= " ++ Generics.show y

-- Direct (non-fold) implementations of applyFD and incrementFD.
applyFD : ℕ → FD → FD → FD
applyFD x subst (＃ i)     = ＃ i
applyFD x subst (a ＃+ b)  = applyFD x subst a ＃+ applyFD x subst b
applyFD x subst (a ＃- b)  = applyFD x subst a ＃- applyFD x subst b
applyFD x subst (a ＃* b)  = applyFD x subst a ＃* applyFD x subst b
applyFD x subst (div a b) = div (applyFD x subst a) (applyFD x subst b)
applyFD x subst (varFD n) = if x ≡ᵇ n then subst else varFD n

equalInt : Int → Int → Bool
equalInt (pos x) (pos y) = x ≡ᵇ y
equalInt (negsuc x) (negsuc y) = x ≡ᵇ y
equalInt _ _ = false

zipMatchFD : FD → FD → (Maybe ∘ List ∘ ℒ) FD
zipMatchFD (＃ x) (＃ y) = if (equalInt x y) then just [] else nothing
zipMatchFD (a ＃+ b) (x ＃+ y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD (a ＃- b) (x ＃- y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD (a ＃* b) (x ＃* y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD (div a b) (div x y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD _ _ = nothing

incrementFD : ℕ → FD → FD
incrementFD x (＃ i)     = ＃ i
incrementFD x (a ＃+ b)  = incrementFD x a ＃+ incrementFD x b
incrementFD x (a ＃- b)  = incrementFD x a ＃- incrementFD x b
incrementFD x (a ＃* b)  = incrementFD x a ＃* incrementFD x b
incrementFD x (div a b) = div (incrementFD x a) (incrementFD x b)
incrementFD x (varFD n) = varFD (x + n)

-- Manual fold for ℒFD.
foldℒFD :
  ∀ {A : Set}
  → (FD → FD → A)        -- ≤FD
  → (FD → FD → A)        -- ≥FD
  → ℒFD → A
foldℒFD f₁ f₂ (a ≤FD b) = f₁ a b
foldℒFD f₁ f₂ (a ≥FD b) = f₂ a b

applyℒFD : ℕ → FD → ℒFD → ℒFD
applyℒFD x subst (a ≤FD b) = applyFD x subst a ≤FD applyFD x subst b
applyℒFD x subst (a ≥FD b) = applyFD x subst a ≥FD applyFD x subst b

zipMatchℒFD : ℒFD → ℒFD → (Maybe ∘ List ∘ ℒ) FD
zipMatchℒFD (x ≤FD y) (a ≤FD b) = just (x =ℒ a ∷ y =ℒ b ∷ [])
zipMatchℒFD (x ≥FD y) (a ≥FD b) = just (x =ℒ a ∷ y =ℒ b ∷ [])
zipMatchℒFD _ _ = nothing

incrementℒFD : ℕ → ℒFD → ℒFD
incrementℒFD x (a ≤FD b) = incrementFD x a ≤FD incrementFD x b
incrementℒFD x (a ≥FD b) = incrementFD x a ≥FD incrementFD x b