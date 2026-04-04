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

instance  ftUtilsFD : FTUtils FD
          ftUtilsFD = deriveFTUtils FDD

instance  ftUtilsℒFD : FTUtils ℒFD
          ftUtilsℒFD = deriveFTUtils ℒFDD

foldFD = deriveFold FDD

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

applyFD : ℕ → FD → FD → FD
applyFD x subst = foldFD ＃_ _＃+_ _＃-_ _＃*_ div (λ y → if x ≡ᵇ y then subst else (varFD y))

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
incrementFD x = foldFD ＃_ _＃+_ _＃-_ _＃*_ div (λ y → varFD (x + y))

foldℒFD = deriveFold ℒFDD

applyℒFD : ℕ → FD → ℒFD → ℒFD
applyℒFD x subst = foldℒFD (λ a b → applyFD x subst a ≤FD applyFD x subst b) (λ a b → applyFD x subst a ≥FD applyFD x subst b)

zipMatchℒFD : ℒFD → ℒFD → (Maybe ∘ List ∘ ℒ) FD
zipMatchℒFD (x ≤FD y) (a ≤FD b) = just (x =ℒ a ∷ y =ℒ b ∷ [])
zipMatchℒFD (x ≥FD y) (a ≥FD b) = just (x =ℒ a ∷ y =ℒ b ∷ [])
zipMatchℒFD _ _ = nothing

incrementℒFD : ℕ → ℒFD → ℒFD
incrementℒFD x = foldℒFD (λ a b → incrementFD x a ≤FD incrementFD x b) (λ a b → incrementFD x a ≥FD incrementFD x b)