module Common.utilities where

open import Common.types
open import Term.types
open import Data.Bool
open import Data.Nat 
  using (ℕ; _≡ᵇ_; _⊓_; _+_)
open import Data.List 
  using (List; []; _∷_; map; any; all)
open import Data.Maybe 
  using (Maybe; just; nothing)

LogicVarTerm : Set
LogicVarTerm = LogicVar (Term LogicVar)

{-# TERMINATING #-}
mapLogicVarTerm : (LogicVarTerm → LogicVarTerm) → LogicVarTerm → LogicVarTerm
mapTerm : (LogicVarTerm → LogicVarTerm) → Term LogicVar → Term LogicVar

mapLogicVarTerm f (var x) = f (var x)
mapLogicVarTerm f (const t) = const (mapTerm f t)

mapTerm f (atomT s args) = atomT s (Data.List.map (mapLogicVarTerm f) args)

-- generic apply function applyᵥ extended by term.

{-# TERMINATING #-}
applyInTerm : ℕ → LogicVar (Term LogicVar) → Term LogicVar → Term LogicVar
applyInLogicVar : ℕ → LogicVar (Term LogicVar) → LogicVar (Term LogicVar) → LogicVar (Term LogicVar)

applyInTerm x te (atomT head args) = atomT head (Data.List.map (applyInLogicVar x te) args)

applyInLogicVar x te (var nothing) = var nothing
applyInLogicVar x te (var (just y)) with x ≡ᵇ y
... | true = te
... | false = var (just y)
applyInLogicVar x te (const t) = const (applyInTerm x te t)

{-# TERMINATING #-}
applyᵥ : {c : 𝒞} {hv : HasVariables} → ℕ → LogicVar (⟦ c ⟧₍𝑑₎ LogicVar) → ⟦ hv ⟧ᵥ → ⟦ hv ⟧ᵥ

applyᵥ {term} {domainExpr term} = applyInLogicVar

applyᵥ {_} {expr _} k te (domainExpr t) = domainExpr (applyᵥ k te t)

applyᵥ {_} {domainConstraint _} k te (e₁ =ℒ e₂) = applyᵥ k te e₁ =ℒ applyᵥ k te e₂

applyᵥ {_} {atom _} k te (mkAtom s args) =
  mkAtom s (applyᵥ k te args)

applyᵥ {_} {literal _} k te (atomLiteral a) = atomLiteral (applyᵥ k te a)
applyᵥ {_} {literal _} k te (𝓁Literal ℓ)    = 𝓁Literal (applyᵥ k te ℓ)

applyᵥ {_} {clause _} k te (head :- body) =
  applyᵥ k te head :- Data.List.map (applyᵥ k te) body

applyᵥ {_} {listOf _} k te xs =
  Data.List.map (applyᵥ k te) xs

-- generic occurs function occursᵥ extended by term.

{-# TERMINATING #-}
occursInTerm : ℕ → Term LogicVar → Bool
occursInLogicVar : ℕ → LogicVar (Term LogicVar) → Bool

occursInTerm x (atomT _ args) = any (occursInLogicVar x) args

occursInLogicVar x (var nothing) = false
occursInLogicVar x (var (just y)) = x ≡ᵇ y
occursInLogicVar x (const t) = occursInTerm x t

{-# TERMINATING #-}
occursᵥ : {hv : HasVariables} → ℕ → ⟦ hv ⟧ᵥ → Bool

occursᵥ {domainExpr term} = occursInLogicVar

occursᵥ {expr _} k (domainExpr t) = occursᵥ k t

occursᵥ {domainConstraint _} k (e₁ =ℒ e₂) = occursᵥ k e₁ ∨ occursᵥ k e₂

occursᵥ {atom _} k (mkAtom s args) = occursᵥ k args

occursᵥ {literal _} k (atomLiteral a) = occursᵥ k a
occursᵥ {literal _} k (𝓁Literal ℓ)    = occursᵥ k ℓ

occursᵥ {clause _} k (head :- body) =
  occursᵥ k head ∨ any (occursᵥ k) body

occursᵥ {listOf _} k xs =
  any (occursᵥ k) xs

-- generic increment function incrementᵥ extended by term.

{-# TERMINATING #-}
incrementLogicVar : ℕ → LogicVar (Term LogicVar) → LogicVar (Term LogicVar)
incrementTerm : ℕ → Term LogicVar → Term LogicVar

incrementLogicVar k (var nothing)    = var nothing
incrementLogicVar k (var (just n))   = var (just (n + k))
incrementLogicVar k (const t)        = const (incrementTerm k t)

incrementTerm k (atomT s args)    = atomT s (Data.List.map (incrementLogicVar k) args)

maybeMax : Maybe ℕ → Maybe ℕ → Maybe ℕ
maybeMax nothing  y         = y
maybeMax x        nothing   = x
maybeMax (just x) (just y)  = just (x Data.Nat.⊔ y)

maxVarLogicVarTerm : LogicVar (Term LogicVar) → Maybe ℕ
maxVarTerm : Term LogicVar → Maybe ℕ
maxVarLogicVars : List (LogicVar (Term LogicVar)) → Maybe ℕ

maxVarLogicVarTerm (var nothing) = nothing
maxVarLogicVarTerm (var (just x)) = just x
maxVarLogicVarTerm (const t) = maxVarTerm t

maxVarTerm (atomT _ args) = maxVarLogicVars args

maxVarLogicVars [] = nothing
maxVarLogicVars (x ∷ xs) = maybeMax (maxVarLogicVarTerm x) (maxVarLogicVars xs)

{-# TERMINATING #-}
incrementLogicVarTerm : ℕ → LogicVar (Term LogicVar) → LogicVar (Term LogicVar)
incrementLogicVarTerm k (var nothing) = var nothing
incrementLogicVarTerm k (var (just x)) = var (just (x + k))
incrementLogicVarTerm k (const t) = const (mapTerm (incrementLogicVarTerm k) t)

{-# TERMINATING #-}
incrementᵥ : {hv : HasVariables} → ℕ → ⟦ hv ⟧ᵥ → ⟦ hv ⟧ᵥ

incrementᵥ {domainExpr term} = incrementLogicVarTerm

incrementᵥ {expr _} k (domainExpr t) = domainExpr (incrementᵥ k t)

incrementᵥ {domainConstraint _} k (e₁ =ℒ e₂) = incrementᵥ k e₁ =ℒ incrementᵥ k e₂

incrementᵥ {atom _} k (mkAtom s args) =
  mkAtom s (incrementᵥ k args)

incrementᵥ {literal _} k (atomLiteral a) = atomLiteral (incrementᵥ k a)
incrementᵥ {literal _} k (𝓁Literal ℓ)    = 𝓁Literal (incrementᵥ k ℓ)

incrementᵥ {clause _} k (head :- body) =
  incrementᵥ k head :- Data.List.map (incrementᵥ k) body

incrementᵥ {listOf _} k xs =
  Data.List.map (incrementᵥ k) xs

-- generic maxVar function maxVarᵥ extended by term.

maxVarᵥ : {hv : HasVariables} → ⟦ hv ⟧ᵥ → Maybe ℕ

maxVarᵥ {domainExpr term} = maxVarLogicVarTerm

maxVarᵥ {expr _} (domainExpr t) = maxVarᵥ t

maxVarᵥ {domainConstraint _} (e₁ =ℒ e₂) = maybeMax (maxVarᵥ e₁) (maxVarᵥ e₂)

maxVarᵥ {atom _} (mkAtom _ args) =
  maxVarᵥ args

maxVarᵥ {literal _} (atomLiteral a) = maxVarᵥ a
maxVarᵥ {literal _} (𝓁Literal ℓ)    = maxVarᵥ ℓ

maxVarᵥ {clause _} (head :- body) =
  maybeMax (maxVarᵥ head) (maxVarᵥ body)

maxVarᵥ {listOf _} []       = nothing
maxVarᵥ {listOf _} (x ∷ xs) = maybeMax (maxVarᵥ x) (maxVarᵥ xs)