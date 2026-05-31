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
  zero   : NatLogic
  suc    : NatLogic → NatLogic
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
          makeVarNat .new   = varNat 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

-- Manual FTUtils for NatLogic.
instance ftUtilsNat : FTUtils NatLogic

         ftUtilsNat .functor zero       = "zero"
         ftUtilsNat .functor (suc _)    = "suc"
         ftUtilsNat .functor (varNat _) = "varNat"

         ftUtilsNat .varName zero       = nothing
         ftUtilsNat .varName (suc _)    = nothing
         ftUtilsNat .varName (varNat n) = just n

         ftUtilsNat .occurs _ zero       = false
         ftUtilsNat .occurs n (suc x)    = occurs ⦃ ftUtilsNat ⦄ n x
         ftUtilsNat .occurs n (varNat m) = n ≡ᵇ m

         ftUtilsNat .collectVars zero       = []
         ftUtilsNat .collectVars (suc x)    = collectVars ⦃ ftUtilsNat ⦄ x
         ftUtilsNat .collectVars (varNat n) = n ∷ []

         ftUtilsNat .getNat _ = nothing

instance  decNat : DecEq NatLogic
          decNat = deriveDecEq natD

instance  showNat : Show NatLogic
          showNat = deriveShow natD

-- Manual fold for NatLogic.
foldNat :
  ∀ {A : Set}
  → A                  -- zero
  → (A → A)            -- suc
  → (ℕ → A)            -- varNat
  → NatLogic → A
foldNat fz fs fv zero       = fz
foldNat fz fs fv (suc x)    = fs (foldNat fz fs fv x)
foldNat fz fs fv (varNat n) = fv n

-- Direct (non-fold) implementations.
applyNat : ℕ → NatLogic → NatLogic → NatLogic
applyNat x subst zero       = zero
applyNat x subst (suc y)    = suc (applyNat x subst y)
applyNat x subst (varNat n) = if x ≡ᵇ n then subst else varNat n

zipMatchNat : NatLogic → NatLogic → (Maybe ∘ List ∘ ℒ) NatLogic
zipMatchNat zero zero       = just []
zipMatchNat (suc x) (suc y) = just (x =ℒ y ∷ [])
zipMatchNat _ _             = nothing

incrementNat : ℕ → NatLogic → NatLogic
incrementNat x zero       = zero
incrementNat x (suc y)    = suc (incrementNat x y)
incrementNat x (varNat n) = varNat (x + n)