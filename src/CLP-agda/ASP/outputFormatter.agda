module ASP.outputFormatter where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Data.Bool hiding (_≟_)
open import Data.String 
  using (String; _==_; _++_)
open import Data.Nat hiding (equal; _≟_)
open import Data.List hiding (_++_)
open import Data.List.Base hiding (_++_)
open import Data.List.Membership.DecSetoid using (_∈?_)
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

open import CLP.outputFormatter

open import ASP.dual

showModifier :
  Modifier → String
showModifier chsMod = "CHS "
showModifier provenMod = "PROVEN "
showModifier noneMod = ""

showMaybe : 
  {Atom : Set}
  → ⦃ Show Atom ⦄
  → Maybe Atom 
  → String
showMaybe nothing = ""
showMaybe ⦃ sh ⦄ (just x) = Generics.show ⦃ sh ⦄ x

groundAtom :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄ 
  → List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
  → ASPAtom Atom 𝒞 Code Constraint
  → ASPAtom Atom 𝒞 Code Constraint
groundAtom {Atom}{C}{Code}{Constraint} ⦃ aspAt ⦄ constraints at =
  foldr substituteOne at 
    ((filterᵇ (λ { (_:-:_ _ x) → (is-just ∘ varName) x }) ∘ collectLeaves ∘ atom) at)
  where
    substituteOne : Σᵢ C Code Code Constraint 
                  → ASPAtom Atom C Code Constraint 
                  → ASPAtom Atom C Code Constraint
    substituteOne (_:-:_ c x) acc with varName x
    ... | nothing = acc
    ... | just nam with findᵇ (λ { (inj₁ (_:-:_ _ (n , _))) → n ≡ᵇ nam 
                                  ; (inj₂ (_:-:_ _ (n , _))) → n ≡ᵇ nam }) constraints
    ...   | nothing = acc
    ...   | just (inj₁ (_:-:_ c′ (_ , y))) = apply aspAt c′ nam y acc
    ...   | just (inj₂ (_:-:_ c′ (_ , y))) = apply aspAt c′ nam y acc

addToJustification : 
  ∀ {Atom 𝒞 Code Constraint}
  → Modifier
  → ℕ
  → ASPAtom Atom 𝒞 Code Constraint
  → ⦃ Show (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄ 
  → List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
  → String
addToJustification {_}{C}{Code}{Constraint} modif n at ⦃ sh ⦄ ⦃ inst ⦄ ⦃ aspAt ⦄ constraints = 
  "\n" Data.String.++ (Data.String.concat ∘ replicate n) " " Data.String.++ showModifier modif Data.String.++ 
  (Generics.show ⦃ sh ⦄ ∘ groundAtom constraints) at

{-# TERMINATING #-}
showJustification : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ Show (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄ 
  → ℕ
  → List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
  → Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) × Modifier × (ASPAtom Atom 𝒞 Code Constraint))
  → String
showJustification n bindings (node (con , modif , at) ys) = 
  addToJustification modif n at bindings ++ (joinWith "" ∘ Data.List.map (formatOutput false [])) con ++ (joinWith "" ∘ Data.List.map (showJustification (suc n) bindings)) ys 

aspFormat : 
  ∀ {Atom 𝒞 Code Constraint}
  → (ASPAtom Atom 𝒞 Code Constraint → Bool)
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ Show (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄ 
  → (ASPUtils Atom 𝒞 Code Constraint × List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint) × List (Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) × Modifier × (ASPAtom Atom 𝒞 Code Constraint)))) × 
    (List ∘ List) ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
  → String
aspFormat {Atom}{C}{Code}{Constraint} showAtom ⦃ inst ⦄ ⦃ sho ⦄ ((_ , chs , _ , justification) , (constraints ∷ _)) = 
  "CHS:\n" ++ (joinWith ", " ∘ 
              Data.List.map (Generics.show ⦃ sho ⦄ ∘ groundAtom constraints) ∘ filterᵇ showAtom) chs ++ 
  "\nJustification:\n" ++ (joinWith "\n" ∘ Data.List.map (showJustification 0 constraints)) justification
aspFormat _ _ = "unsat"