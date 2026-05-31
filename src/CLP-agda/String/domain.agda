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
  ~_       : String → StringLogic
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
          makeVarString .new   = varString 0

instance  unifyDisunifyℕ : FTUtils ℕ
          unifyDisunifyℕ = deriveFTUtils ℕD

instance  decStrin : DecEq String
          decStrin .Generics._≟_ = Data.String._≟_

instance  showStrin : Show String
          showStrin .Generics.show = id

instance  ftUtilsStrin : FTUtils String
          ftUtilsStrin .functor       = id
          ftUtilsStrin .varName _     = nothing
          ftUtilsStrin .occurs _ _    = false
          ftUtilsStrin .collectVars _ = []
          ftUtilsStrin .getNat _      = nothing

-- Manual FTUtils for StringLogic.
instance ftUtilsString : FTUtils StringLogic
         -- The "functor" is a textual identifier for the
         -- top-level constructor.  For a ground string we use
         -- the string itself; for a variable we tag it.
         ftUtilsString .functor (~ s)         = s
         ftUtilsString .functor (varString n) = "varString"

         ftUtilsString .varName (~ _)         = nothing
         ftUtilsString .varName (varString n) = just n

         ftUtilsString .occurs _ (~ _)         = false
         ftUtilsString .occurs n (varString m) = n ≡ᵇ m

         ftUtilsString .collectVars (~ _)         = []
         ftUtilsString .collectVars (varString n) = n ∷ []

         ftUtilsString .getNat _ = nothing

instance decString : DecEq StringLogic
         decString = deriveDecEq stringD

instance showString : Show StringLogic
         showString = deriveShow stringD

-- Manual fold for StringLogic.
foldString :
  ∀ {A : Set}
  → (String → A)         -- ground string
  → (ℕ → A)              -- varString
  → StringLogic → A
foldString f₁ f₂ (~ s)         = f₁ s
foldString f₁ f₂ (varString n) = f₂ n

-- Direct (non-fold) implementations of applyString
applyString : ℕ → StringLogic → StringLogic → StringLogic
applyString x subst (~ s)         = ~ s
applyString x subst (varString n) = if x ≡ᵇ n then subst else varString n

zipMatchString : StringLogic → StringLogic → (Maybe ∘ List ∘ ℒ) StringLogic
zipMatchString (~ x) (~ y) = if x == y then just [] else nothing
zipMatchString _ _         = nothing

incrementString : ℕ → StringLogic → StringLogic
incrementString x (~ s)         = ~ s
incrementString x (varString n) = varString (x + n)