{-# OPTIONS --safe #-}
module Term.ftUtilsDerivation where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers

open import Data.Nat 
  using (ℕ; _≡ᵇ_)
open import Data.Bool
import Data.Vec.Base as Vec
open import Agda.Builtin.String
import Data.String   as String hiding (length; _++_)
open import Data.List
open import Data.Char
open import Data.Maybe as Maybe
open import Data.These hiding (alignWith)

open String hiding (show)


record FTUtils {l} (A : Set l) : Set l where
  field
    functor : A → String
    getNat : A → Maybe ℕ
    varName : A → Maybe ℕ
    occurs : ℕ → A → Bool
    collectVars : A → List ℕ
open FTUtils ⦃...⦄ public

-- varName
-- functor
-- zipMatch
-- applyᵥ
-- occursᵥ
-- incrementᵥ
-- collectVarsᵥ

beginsWithList : List Char → List Char → Bool
beginsWithList _ [] = true
beginsWithList [] _ = false
beginsWithList (x ∷ xs) (y ∷ ys) = (toℕ x ≡ᵇ toℕ y) ∧ beginsWithList xs ys

beginsWith : String → String → Bool
beginsWith x y = beginsWithList (primStringToList y) (primStringToList x)

module _
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc A)
  (open HasDesc H)
  (open Helpers P I FTUtils (const ⊤) (λ _ → Liftω ⊤))
  where

  FTUtilsHelpers : ∀ p → Setω
  FTUtilsHelpers p = Helpers p D

  module _ {p} (helpers : FTUtilsHelpers p) where

    variable
      V : ExTele P
      v : ⟦ V ⟧tel p
      i : ⟦ I ⟧tel p

    functorData-wf : (x : ⟦ D ⟧Data A′ (p , i))
                    → AllDataω Acc D x
                    → String

    functor-wf : (x : A′ (p , i)) → Acc x → String

    functor-wf x (acc a) = functorData-wf (split x) a

    functorData-wf (k , x) a = Vec.lookup names k

    functor′ : A′ (p , i) → String
    functor′ x = functor-wf x (wf x)

    getNatData-wf : (x : ⟦ D ⟧Data A′ (p , i))
                    → AllDataω Acc D x
                    → Maybe ℕ

    getNat-wf : (x : A′ (p , i)) → Acc x → Maybe ℕ

    getNat-wf x (acc a) = getNatData-wf (split x) a

    getNatIndArg : (C : ConDesc P V I)
                  (x : ⟦ C ⟧IndArg A′ (p , v))
                → AllIndArgω Acc C x
                → Maybe ℕ

    getNatCon : (C : ConDesc P V I)
              (H : ConHelper p C)
              (x : ⟦ C ⟧Con A′ (p , v , i))
            → AllConω Acc C x
            → Maybe ℕ

    getNatData-wf (k , x) a with Vec.lookup names k
    getNatData-wf (k , x) a | "zero" = just zero
    getNatData-wf (k , x) a | "suc" with getNatCon (lookupCon D k) (lookupHelper helpers k) x a
    getNatData-wf (k , x) a | "suc" | just n = just (suc n)
    getNatData-wf (k , x) a | "suc" | nothing = nothing
    getNatData-wf (k , x) a | _ = nothing
  
    getNatIndArg (var _) x a = getNat-wf x a
    getNatIndArg (π ia S C) x a = nothing
    getNatIndArg (A ⊗ B) (xa , xb) (aa , ab)
      = getNatIndArg A xa aa

    getNatCon (var _) var refl tt = nothing
    getNatCon ._ (pi-irr ⦃ _ ⦄ ⦃ H ⦄) (s , x) a
      = nothing
    getNatCon ._ (pi-rel ⦃ S ⦄ ⦃ H ⦄) (s , x) a
      = nothing
    getNatCon ._ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb) (aa , ab)
      = getNatIndArg A xa aa

    getNat′ : A′ (p , i) → Maybe ℕ
    getNat′ x = getNat-wf x (wf x)

    varNameData-wf : (x : ⟦ D ⟧Data A′ (p , i))
                    → AllDataω Acc D x
                    → Maybe ℕ

    varName-wf : (x : A′ (p , i)) → Acc x → Maybe ℕ

    varName-wf x (acc a) = varNameData-wf (split x) a

    varNameIndArg : (C : ConDesc P V I)
                  (x : ⟦ C ⟧IndArg A′ (p , v))
                → AllIndArgω Acc C x
                → Maybe ℕ

    varNameCon : (C : ConDesc P V I)
              (H : ConHelper p C)
              (x : ⟦ C ⟧Con A′ (p , v , i))
            → AllConω Acc C x
            → Maybe ℕ

    varNameData-wf (k , x) a = 
      if (beginsWith "var" ∘ Vec.lookup names) k
      then varNameCon (lookupCon D k) (lookupHelper helpers k) x a
      else nothing
  
    varNameIndArg (var _) x a = varName-wf x a
    varNameIndArg (π ia S C) x a = nothing
    varNameIndArg (A ⊗ B) (xa , xb) (aa , ab)
      = nothing

    varNameCon (var _) var refl tt = nothing
    varNameCon ._ (pi-irr ⦃ _ ⦄ ⦃ H ⦄) (s , x) a
      = nothing
    varNameCon ._ (pi-rel ⦃ S ⦄ ⦃ H ⦄) (s , x) a
      = getNat ⦃ S ⦄ s
    varNameCon ._ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb) (aa , ab)
      = nothing

    varName′ : A′ (p , i) → Maybe ℕ
    varName′ x = varName-wf x (wf x)

    occursData-wf : (x : ⟦ D ⟧Data A′ (p , i))
                → AllDataω Acc D x
                → ℕ → Bool

    occurs-wf : (x : A′ (p , i)) → Acc x → ℕ → Bool
    occurs-wf x (acc a) va = (is-just (varName-wf x (acc a) >>= (λ { y → if y ≡ᵇ va then just y else nothing }))) ∨ occursData-wf (split x) a va

    occursData-wf (k , x) a = occursCon (lookupCon D k) (lookupHelper helpers k) x a
      where
        occursIndArg : (C : ConDesc P V I)
                     (x : ⟦ C ⟧IndArg A′ (p , v))
                   → AllIndArgω Acc C x
                   → ℕ → Bool
        occursIndArg (var _) x a n = occurs-wf x a n
        occursIndArg (π ia S C) x a _ = false
        occursIndArg (A ⊗ B) (xa , xb) (aa , ab) n
          = occursIndArg A xa aa n ∨ occursIndArg B xb ab n

        occursCon : (C : ConDesc P V I)
                  (H : ConHelper p C)
                  (x : ⟦ C ⟧Con A′ (p , v , i))
                → AllConω Acc C x
                → ℕ → Bool
        occursCon ._ var refl tt _ = false
        occursCon ._ (pi-irr ⦃ _ ⦄ ⦃ H ⦄) (s , x) a n
          = occursCon _ H x a n
        occursCon ._ (pi-rel ⦃ S ⦄ ⦃ H ⦄) (s , x) a n
          = occurs ⦃ S ⦄ n s ∨ occursCon _ H x a n
        occursCon ._ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb) (aa , ab) n
          = occursIndArg A xa aa n ∨ occursCon B HB xb ab n

    occurs′ : (x : A′ (p , i)) → ℕ → Bool
    occurs′ x = occurs-wf x (wf x)

    collectVarsData-wf : (x : ⟦ D ⟧Data A′ (p , i))
                → AllDataω Acc D x
                → List ℕ

    collectVars-wf : (x : A′ (p , i)) → Acc x → List ℕ
    collectVars-wf x (acc a) = collectVarsData-wf (split x) a -- (varName-wf x (acc a) >>= (λ { nothing → []; just x → x ∷ [] })) ++ collectVarsData-wf (split x) a

    collectVarsData-wf (k , x) a = collectVarsCon (lookupCon D k) (lookupHelper helpers k) x a
      where
        collectVarsIndArg : (C : ConDesc P V I)
                     (x : ⟦ C ⟧IndArg A′ (p , v))
                   → AllIndArgω Acc C x
                   → List ℕ
        collectVarsIndArg (var _) x a = collectVars-wf x a
        collectVarsIndArg (π ia S C) x a = []
        collectVarsIndArg (A ⊗ B) (xa , xb) (aa , ab)
          = collectVarsIndArg A xa aa ++ collectVarsIndArg B xb ab

        collectVarsCon : (C : ConDesc P V I)
                  (H : ConHelper p C)
                  (x : ⟦ C ⟧Con A′ (p , v , i))
                → AllConω Acc C x
                → List ℕ
        collectVarsCon ._ var refl tt = []
        collectVarsCon ._ (pi-irr ⦃ _ ⦄ ⦃ H ⦄) (s , x) a
          = collectVarsCon _ H x a
        collectVarsCon ._ (pi-rel ⦃ S ⦄ ⦃ H ⦄) (s , x) a
          = collectVars ⦃ S ⦄ s ++ collectVarsCon _ H x a
        collectVarsCon ._ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb) (aa , ab)
          = collectVarsIndArg A xa aa ++ collectVarsCon B HB xb ab

    collectVars′ : (x : A′ (p , i)) → List ℕ
    collectVars′ x = collectVars-wf x (wf x)

  deriveFTUtils : ∀ {p} ⦃ SH : FTUtilsHelpers p ⦄ {i} → FTUtils (A′ (p , i))
  deriveFTUtils ⦃ SH ⦄ .functor = functor′ SH
  deriveFTUtils ⦃ SH ⦄ .getNat = getNat′ SH
  deriveFTUtils ⦃ SH ⦄ .varName = varName′ SH
  deriveFTUtils ⦃ SH ⦄ .occurs = λ { x y → occurs′ SH y x }
  deriveFTUtils ⦃ SH ⦄ .collectVars = collectVars′ SH