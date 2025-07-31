module CLP.clp where

open import Common.types
open import Common.solver
open import Common.utilities
open import Views.find
open import Views.findall
open import Data.Bool
open import Data.String 
  using (String; _==_)
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.List 
  using (List; []; _∷_; _++_; map; length; zip; zipWith; concat)
open import Data.Maybe 
  using (Maybe; just; nothing; map)
open import Data.Product 
  using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)

-- For checking if an atom can unify with a clause
_⇔_ : {c : 𝒞} → Atom c → Clause c → Bool
mkAtom name₀ args₀ ⇔ (mkAtom name₁ args₁ :- _) = (name₀ == name₁) ∧ (length args₀ ≡ᵇ length args₁)

-- TO DO: use Maybe.map to erase second pattern match
bindAndRename : {c : 𝒞} → Atom c → Maybe ℕ → Clause c → List (Literal c)
bindAndRename {c} (mkAtom _ exprs₀) nothing  (mkAtom _ exprs₁ :- l) = 
  zipWith (λ x y → 𝓁Literal (x =ℒ y)) exprs₀ exprs₁ ++ l
bindAndRename {c} (mkAtom _ exprs₀) (just n) (mkAtom _ exprs₁ :- l) = 
  zipWith (λ x y → 𝓁Literal (x =ℒ y)) exprs₀ (incrementᵥ (suc n) exprs₁) ++ incrementᵥ (suc n) l

-- Removes variables that are not asked for in a given context
removeUnusedVars : {c : 𝒞} → List (Literal c) → Subst c → Subst c
removeUnusedVars right [] = []
removeUnusedVars right ((x , t) ∷ xs) with occursᵥ x right
... | true = (x , t) ∷ (removeUnusedVars right xs)
... | false = removeUnusedVars right xs

-- Generic evaluation function, terminating required because this requires Turing-completeness
{-# TERMINATING #-}
eval : 
  {c : 𝒞}
  → List (Clause c)
  → List (Literal c)
  → List (ℒ c)
  → (findAll : Bool)
  → Subst c
  → if findAll then List (Subst c) else Maybe (Subst c) -- type depends on whether findall mode is activated

-- base cases for the two modi
eval program [] right true subst = subst ∷ []
eval program [] right false subst = just subst

-- cases for splitting an atom into the body of its unified clause
eval     program         (atomLiteral at ∷ left) right _ _ with findAll ((_⇔_) at) program
eval {c} .(forget split) (atomLiteral at ∷ left) right false subst | matches split _ _ 
  with Data.List.map (λ {cl → 
    Data.Maybe.map
      (removeUnusedVars (atomLiteral at ∷ left ++ Data.List.map 𝓁Literal right)) 
        (eval
          (forget split)
          ((bindAndRename at (maybeMax (maxVarᵥ (atomLiteral at ∷ left)) (maxVarᵥ right)) cl) ++ left)
          right
          false
          subst)})
      (first split)

eval {c} .(forget split) (atomLiteral at ∷ left) right false _ | matches split _ _
  | derivations with find (λ {(just _) → true ; nothing → false}) derivations
eval     .(forget split) (atomLiteral at ∷ left) right _ _ | matches split _ _
  | .(_ ++ successful-derivation ∷ _) | found before successful-derivation _ after = successful-derivation
eval     .(forget split)        (atomLiteral at ∷ left) right _ _ | matches split _ _
  | no-successful-derivations         | not-found _ = nothing

eval {c} .(forget split) (atomLiteral at ∷ left) right true subst | matches split _ _ 
  with Data.List.map (λ {cl → 
    Data.List.map
      (removeUnusedVars (atomLiteral at ∷ left ++ Data.List.map 𝓁Literal right)) 
        (eval
          (forget split)
          ((bindAndRename at (maybeMax (maxVarᵥ (atomLiteral at ∷ left)) (maxVarᵥ right)) cl) ++ left)
          right
          true
          subst)})
      (first split)
eval {c} .(forget split) (atomLiteral at ∷ left) right true _ | matches split _ _
  | derivations with findAll (λ {(_ ∷ _) → true ; [] → false}) derivations
eval     .(forget split) (atomLiteral at ∷ left) right _ _ | matches split _ _
  | .(forget splitNondet) | matches splitNondet _ _ = concat (first splitNondet)

-- cases for addition of domain constraints to the right side for preliminary consistency check by solver
eval program (𝓁Literal cnstr ∷ left) right false subst with solve (cnstr ∷ right) refl subst
eval program (𝓁Literal cnstr ∷ left) right false subst | just newSubst = eval program left (cnstr ∷ right) false newSubst
eval program (𝓁Literal cnstr ∷ left) right false subst | nothing = nothing

eval program (𝓁Literal cnstr ∷ left) right true subst with solve (cnstr ∷ right) refl subst
eval program (𝓁Literal cnstr ∷ left) right true subst | just newSubst = eval program left (cnstr ∷ right) true newSubst
eval program (𝓁Literal cnstr ∷ left) right true subst | nothing = []