module ASP.types where

data ASPAtom (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  wrap : Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → ASPAtom Atom 𝒞 Code Constraint
  forAll : Σᵢ 𝒞 Code Code Constraint → ASPAtom Atom 𝒞 Code Constraint → ASPAtom Atom 𝒞 Code Constraint
  nmrCheck : ASPAtom Atom 𝒞 Code Constraint
  chk : ℕ → List (Σᵢ 𝒞 Code Code Constraint) → ASPAtom Atom 𝒞 Code Constraint

record ASPUtils (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    isNot : A → Bool
    not : A → A

open ASPUtils ⦃...⦄ public

