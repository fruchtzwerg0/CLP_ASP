{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup; pi; curry)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers


module Term.chatGpt
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
  {p c} {X : Pred′ I λ i → Set c}
  where

open HasDesc H

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

X′ : ⟦ I ⟧tel p → Set c
X′ i = unpred′ I _ X i


------------------------
-- Types of the algebra

levelAlg : ConDesc P V I → Level
levelAlg (var _) = c
levelAlg (π {ℓ} _ _ C) = ℓ ⊔ levelAlg C
levelAlg (A ⊗ B) = levelAlg B

AlgCon : (C : ConDesc P V I) → ⟦ V ⟧tel p → Set (levelAlg C)
AlgCon (var f) v = X′ (f (p , v))
AlgCon (π ia S C) v = Π< ia > (S (p , v)) λ s → AlgCon C (v , s)
AlgCon (A ⊗ B) v = AlgCon B v

Algebra : ∀ k → Set (levelAlg (lookupCon D k))
Algebra k = AlgCon (lookupCon D k) tt

----------------
-- Generic fold

module _ (algs : Els Algebra) where

  flatFold-wf : (x : A′ (p , i)) → Acc x → X′ i

  flatFoldData-wf : (x : ⟦ D ⟧Data A′ (p , i)) → AllDataω Acc D x → X′ i
  flatFoldData-wf {i} (k , x) = flatFoldCon (lookupCon D k) (algs k) x
    where
      flatFoldCon : (C   : ConDesc P V I)
                (alg : AlgCon C v)
                (x   : ⟦ C ⟧Con A′ (p , v , i))
              → AllConω Acc C x
              → X′ i
      flatFoldCon (var _) alg refl _ = alg
      flatFoldCon (π ia S C) alg (s , x) a = flatFoldCon C (app< ia > alg s) x a
      flatFoldCon (A ⊗ B) alg (xa , xb) (aa , ab)
        = flatFoldCon B alg xb ab

  flatFold-wf x (acc a) = flatFoldData-wf (split x) a

  flatFold : A′ (p , i) → X′ i
  flatFold x = flatFold-wf x (wf x)

deriveFlatFold : Arrows Algebra (Pred′ I λ i → A′ (p , i) → X′ i)
deriveFlatFold = curryₙ λ m → pred′ I _ λ i → flatFold m