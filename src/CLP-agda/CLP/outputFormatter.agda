module CLP.outputFormatter where

open import CLP.types
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import Data.Bool
open import Data.String 
  using (String; _==_; _++_)
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.Nat.Show renaming (show to showNat)
open import Data.List hiding (_++_)
open import Data.Maybe 
  using (Maybe; just; nothing; map; is-just)
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Function.Base

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

joinWith : String → List String → String
joinWith sep = foldr step ""
  where
    step : String → String → String
    step x "" = x
    step x acc = x ++ sep ++ acc

formatOutput :
  ∀ {𝒞 Code Constraint}
  → (shouldGround : Bool)
  → List ℕ
  → if shouldGround 
    then List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
    else List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → String
formatOutput true relevantVars = 
  joinWith ", " ∘ Data.List.map (λ 
    { (inj₁ (c :-: (n , x))) → "var " ++ showNat n ++ " = " ++ show x ; 
      (inj₂ (c :-: (n , x))) → "var " ++ showNat n ++ " = " ++ show x }) ∘ filterᵇ (λ 
    { (inj₁ (c :-: (n , x))) → any (_≡ᵇ_ n) relevantVars ; 
      (inj₂ (c :-: (n , x))) → any (_≡ᵇ_ n) relevantVars })
formatOutput {C}{Code}{Constraint} false relevantVars = 
  joinWith ", " ∘ Data.List.map (λ 
    { (inj₁ (c :-: (x =ℒ y))) → show x ++ " = " ++ show y ; 
      (inj₁ (c :-: (x ≠ℒ y))) → show x ++ " /= " ++ show y ; 
      (inj₂ (c :-: default x)) → show x ;
      (inj₂ (c :-: dual x)) → "! " ++ show x })