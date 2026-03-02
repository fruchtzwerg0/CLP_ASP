module Bool.domain where

open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.List
open import Function.Base

open import Generics
open import Term.ftUtilsDerivation
open import Term.types

data BoolLogic : Set where
  true : BoolLogic
  false : BoolLogic
  varBool : ℕ → BoolLogic

boolD : HasDesc BoolLogic
boolD = deriveDesc BoolLogic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  makeVarBoolLogic : MakeVar BoolLogic
          makeVarBoolLogic .fresh = varBool
          makeVarBoolLogic .new = varBool 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  unifyDisunifyBoolLogic : FTUtils BoolLogic
          unifyDisunifyBoolLogic = deriveFTUtils boolD

foldBool = deriveFold boolD

applyBool : ℕ → BoolLogic → BoolLogic → BoolLogic
applyBool x subst = foldBool true false (λ y → if x ≡ᵇ y then subst else (varBool y))

zipMatchBool : BoolLogic → BoolLogic → (Maybe ∘ List ∘ ℒ) BoolLogic
zipMatchBool true true = just []
zipMatchBool false false = just []
zipMatchBool _ _ = nothing

incrementBool : ℕ → BoolLogic → BoolLogic
incrementBool x = foldBool true false (λ y → varBool (x + y))