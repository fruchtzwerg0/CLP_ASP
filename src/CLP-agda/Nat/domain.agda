module Nat.domain where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.Maybe
open import Data.List
open import Function.Base

open import Generics
open import CLP.ftUtilsDerivation
open import CLP.types

data NatLogic : Set where
  zero : NatLogic
  suc : NatLogic → NatLogic
  varNat : ℕ → NatLogic

natD : HasDesc NatLogic
natD = deriveDesc NatLogic

ℕD : HasDesc ℕ
ℕD = deriveDesc ℕ

instance  decℕ : DecEq ℕ
          decℕ = deriveDecEq ℕD

instance  showℕ : Show ℕ
          showℕ .Generics.show = Data.Nat.Show.show

instance  makeVarNat : MakeVar NatLogic
          makeVarNat .fresh = varNat
          makeVarNat .new = varNat 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  ftUtilsNat : FTUtils NatLogic
          ftUtilsNat = deriveFTUtils natD

foldNat = deriveFold natD

instance  decNat : DecEq NatLogic
          decNat = deriveDecEq natD

instance  showNat : Show NatLogic
          showNat = deriveShow natD

applyNat : ℕ → NatLogic → NatLogic → NatLogic
applyNat x subst = foldNat zero suc (λ y → if x ≡ᵇ y then subst else (varNat y))

zipMatchNat : NatLogic → NatLogic → (Maybe ∘ List ∘ ℒ) NatLogic
zipMatchNat zero zero = just []
zipMatchNat (suc x) (suc y) = just (x =ℒ y ∷ [])
zipMatchNat _ _ = nothing

incrementNat : ℕ → NatLogic → NatLogic
incrementNat x = foldNat zero suc (λ y → varNat (x + y))