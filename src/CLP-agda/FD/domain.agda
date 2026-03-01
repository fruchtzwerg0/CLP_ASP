module FD.domain where

open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.List
open import Function.Base

open import Generics
open import Term.ftUtilsDerivation
open import Term.types

data FD : Set where
  zero : FD
  suc : FD → FD
  _＃+_ : FD → FD → FD
  _＃-_ : FD → FD → FD
  _＃*_ : FD → FD → FD
  div : FD → FD → FD
  varFD : ℕ → FD

data ℒFD : Set where
  _≤FD_ : FD → FD → ℒFD
  _≥FD_ : FD → FD → ℒFD

pattern _＃≤_ x y = (default (x ≤FD y))
pattern _＃>_ x y = (dual (x ≤FD y))
pattern _＃≥_ x y = (default (x ≥FD y))
pattern _＃<_ x y = (dual (x ≥FD y))

FDD : HasDesc FD
FDD = deriveDesc FD

ℒFDD : HasDesc ℒFD
ℒFDD = deriveDesc ℒFD

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  makeVarFD : MakeVar FD
          makeVarFD .fresh = varFD
          makeVarFD .new = varFD 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  unifyDisunifyFD : FTUtils FD
          unifyDisunifyFD = deriveFTUtils FDD

instance  unifyDisunifyℒFD : FTUtils ℒFD
          unifyDisunifyℒFD = deriveFTUtils ℒFDD

foldFD = deriveFold FDD

applyFD : ℕ → FD → FD → FD
applyFD x subst = foldFD zero suc _＃+_ _＃-_ _＃*_ div (λ y → if x ≡ᵇ y then subst else (varFD y))

zipMatchFD : FD → FD → (Maybe ∘ List ∘ ℒ) FD
zipMatchFD zero zero = just []
zipMatchFD (suc x) (suc y) = just (x =ℒ y ∷ [])
zipMatchFD (a ＃+ b) (x ＃+ y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD (a ＃- b) (x ＃- y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD (a ＃* b) (x ＃* y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD (div a b) (div x y) = just (a =ℒ x ∷ b =ℒ y ∷ [])
zipMatchFD _ _ = nothing

incrementFD : ℕ → FD → FD
incrementFD x = foldFD zero suc _＃+_ _＃-_ _＃*_ div (λ y → varFD (x + y))

foldℒFD = deriveFold ℒFDD

applyℒFD : ℕ → FD → ℒFD → ℒFD
applyℒFD x subst = foldℒFD (λ a b → applyFD x subst a ≤FD applyFD x subst b) (λ a b → applyFD x subst a ≥FD applyFD x subst b)

incrementℒFD : ℕ → ℒFD → ℒFD
incrementℒFD x = foldℒFD (λ a b → incrementFD x a ≤FD incrementFD x b) (λ a b → incrementFD x a ≥FD incrementFD x b)