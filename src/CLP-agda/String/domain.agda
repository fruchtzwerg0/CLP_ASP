module String.domain where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.String
open import Data.Maybe
open import Data.List
open import Function.Base

open import Generics
open import CLP.ftUtilsDerivation
open import CLP.types

data StringLogic : Set where
  ~_ : String → StringLogic
  varString : ℕ → StringLogic

stringD : HasDesc StringLogic
stringD = deriveDesc StringLogic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  decℕ : DecEq ℕ
          decℕ = deriveDecEq ℕD

instance  showℕ : Show ℕ
          showℕ .Generics.show = Data.Nat.Show.show

instance  makeVarString : MakeVar StringLogic
          makeVarString .fresh = varString
          makeVarString .new = varString 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  decStrin : DecEq String
          decStrin .Generics._≟_ = Data.String._≟_

instance  showStrin : Show String
          showStrin .Generics.show = id

instance  ftUtilsStrin : FTUtils String
          ftUtilsStrin .functor = id
          ftUtilsStrin .varName _ = nothing
          ftUtilsStrin .occurs _ _ = false
          ftUtilsStrin .collectVars _ = []
          ftUtilsStrin .getNat _ = nothing

instance  ftUtilsString : FTUtils StringLogic
          ftUtilsString = deriveFTUtils stringD

foldString = deriveFold stringD

instance  decString : DecEq StringLogic
          decString = deriveDecEq stringD

instance  showString : Show StringLogic
          showString = deriveShow stringD

applyString : ℕ → StringLogic → StringLogic → StringLogic
applyString x subst = foldString ~_ (λ y → if x ≡ᵇ y then subst else (varString y))

zipMatchString : StringLogic → StringLogic → (Maybe ∘ List ∘ ℒ) StringLogic
zipMatchString (~ x) (~ y) = if x == y then just [] else nothing
zipMatchString _ _ = nothing

incrementString : ℕ → StringLogic → StringLogic
incrementString x = foldString ~_ (λ y → varString (x + y))