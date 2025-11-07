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

data AspRule (A : Set) : Set where
  not : A → AspRule A

removeHeadUnification : {c : 𝒞} → List (Expr c) → List (Σ (Expr c) Maybe )
removeHeadUnification = foldr (λ { acc arg → if isVar arg ∧ elem arg acc then (suc (maxVarᵥ acc)) ∷ acc else arg ∷ acc }) []

count : ℕ → List ℕ
count (suc x) = x ∷ count x
count zero = []

getNextFreeClauseName : String → ℕ → List (Clause c) → String
getNextFreeClauseName base zero program = if (_≡ᵇ_ 0 ∘ length ∘ filter (λ { (mkAtom name _ :- _) →  base ≡ᵇ name})) program then base else getNextFreeClauseName (base ++ "_") program
getNextFreeClauseName base (suc n) program = if (_≡ᵇ_ 0 ∘ length ∘ filter (λ { (mkAtom name _ :- _) →  base ≡ᵇ name})) program then getNextFreeClauseName base n program else getNextFreeClauseName (base ++ "_") program

unfoldr : {A B : Set} → (B → Maybe (A × B)) → B → List A
unfoldr f seed with f seed
... | nothing        = []
... | just (x , seed') = x ∷ unfoldr f seed'

makeTopLevelBody : {c : 𝒞} → ℕ → ℕ → List (Atom c)
makeTopLevelBody (suc x) argLength = not (mkAtom (getNextFreeClauseName x name) ((count ∘ length) argLength))

without : {A : Set} → (A → A → Dec (A ≡ A)) → List A → List A → List A
without _≟_ xs ys = filter (λ x → not (elem _≟_ x ys)) xs

makeParamUnificationExplicit : {c : 𝒞} → List (Expr c) → List (ℒ c)
makeParamUnificationExplicit ((domainExpr (const x)) ∷ xs) = ((const x) =ℒ ((suc ∘ maxVarᵥ) ((domainExpr (const x)) ∷ xs))) ∷ makeParamUnificationExplicit xs
makeParamUnificationExplicit ((domainExpr (var x)) ∷ xs) = makeParamUnificationExplicit xs
makeParamUnificationExplicit [] = []

collectVarsForForAll : {c : 𝒞} → Clause c → List ℕ
collectVarsForForAll (mkAtom name args :- body) = 
  without _≟_ 
    (collectVarsᵥ (body ++ map 𝓁Literal (makeParamUnificationExplicit args)))
    (collectVarsᵥ (filter isVar args ++ map (λ { (_ =ℒ right) → right }) makeParamUnificationExplicit args))

negateLiteral : {c : 𝒞} → Literal c → Literal c
negateLiteral (atomLiteral atom) = not (atomLiteral atom)
negateLiteral (𝓁Literal (l =ℒ r)) = 𝓁Literal (l ≠ℒ r)

buildNegatedBody : {c : 𝒞} → ℕ → List (Literal c) → List (Literal c)
buildNegatedBody (suc n) lit = negateLiteral lit ∷ buildNegatedBody n
buildNegatedBody (zero) lit = lit ∷ []

applyDeMorgan : {c : 𝒞} → ℕ → Clause c → List (Clause c)
applyDeMorgan n (mkAtom name args :- body) =
  unfoldr (λ { suc x → not (mkAtom (getNextFreeClauseName n name) (unfoldr (λ x → ((just ∘ suc ∘ maxVarᵥ) x , ((just ∘ suc ∘ maxVarᵥ) x) ∷ x)) (collectVarsForForAll (mkAtom name args :- body)))) :-  (reverse ∘ buildNegatedBody (length body - x)) body }) (length body)

buildForAll : {c : 𝒞} → List ℕ → List ℕ → String → Clause c
buildForAll (v ∷ vars) acc name = atomLiteral (mkAtom "forall" (var v ∷ buildForall vars (v ∷ acc) name ∷ []))
buildForAll [] acc name = atomLiteral (not mkAtom name (map var acc))



computeDual : {c : 𝒞} → List (Clause c) → List (Clause c)
computeDual ((mkAtom name args :- body) ∷ xs) = 
  (not (mkAtom name ((count ∘ length) args)) :- makeTopLevelBody ((suc ∘ length) xs)) ∷
  foldr
    (λ {(suc n , (mkAtom name args :- body)) x → 
      (n , if (_≡ᵇ_ 0 ∘ length ∘ collectVarsForForAll) (mkAtom name args :- body)
           then applyDeMorgan ((suc ∘ length) xs - n)
           else (not (mkAtom name (map (suc ∘ maxVarᵥ) (collectVarsForForAll (mkAtom name args :- body)))) :- 
              buildForAll (collectVarsForForAll (mkAtom name args :- body)) [] (getNextFreeClauseName ((suc ∘ length) xs - n) name))
              ∷ applyDeMorgan ((suc ∘ length) xs - n)) (mkAtom name args :- body ++ map 𝓁Literal (makeParamUnificationExplicit args))} )
           (zero , [])
           ((mkAtom name args :- body) ∷ xs)

cForall = ?

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