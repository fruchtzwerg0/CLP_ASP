module ASP.outputFormatter where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Views.find
open import Views.findall
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

aspFormat : 
  ∀ {Atom 𝒞 Code Constraint}
  → (shouldGround : Bool)
  → List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint) × String × 
    List (if shouldGround 
    then List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
    else List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) )
  → String
aspFormat {Atom}{C}{Code}{Constraint} shouldGround (chs , _ , justification , constraints) = 
  "CHS:\n" ++ (joinWith ", " ∘ concat ∘ 
              Data.List.map (λ x → defaultFormat shouldGround (collectVarsᵥ C Code Constraint x) constraints)) chs ++ 
  "Justification:\n" ++ justification