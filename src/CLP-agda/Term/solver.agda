module Term.solver where

open import Common.types
open import Common.utilities
open import Term.types
open import Data.List 
  using (List; []; _∷_; _++_; map; zipWith; length)
open import Data.Maybe 
  using (Maybe; just; nothing)
open import Data.Bool
open import Data.Product
  using (_,_)
open import Data.String 
  using (String; _==_)
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)

-- not yet a clean implementation, planning to write a proof, that after the unification algorithm is done,
-- the left sides can only ever be variables. Second case is here just to shut the compiler up (for now).
toSubst : {c : 𝒞} (right : List (ℒ c)) → Subst c
toSubst ((domainExpr (var (just x)) =ℒ domainExpr t) ∷ xs) = (x , t) ∷ toSubst xs
-- hack
toSubst _ = []

-- Implementation of Algorithm 1 in "An Efficient Unification Algorithm" by A. Martelli & U. Montanari

-- Planning to write a proof that this always terminates. (The proof is in the paper ^)
-- meanwhile shutting the compiler up with TERMINATING
{-# TERMINATING #-}
unifyAcc : List (ℒ term) → List (ℒ term) → Maybe (Subst term)
unifyCaseB : List (ℒ term) → List (ℒ term) → Maybe (Maybe (Subst term))
unifyCaseD : List (ℒ term) → List (ℒ term) → Maybe (Maybe (Subst term))

unifyAcc acc [] = just (toSubst acc)
unifyAcc acc ((domainExpr (const t) =ℒ domainExpr (var x)) ∷ xs) = unifyAcc [] (acc ++ (domainExpr (var x) =ℒ domainExpr (const t)) ∷ xs)
unifyAcc acc ((domainExpr (const (atomT root₀ args₀)) =ℒ domainExpr (const (atomT root₁ args₁))) ∷ xs) with (root₀ == root₁) ∧ (length args₀ ≡ᵇ length args₁)
... | true = unifyAcc [] (acc ++ ((zipWith (λ x y → (domainExpr x =ℒ domainExpr y)) args₀ args₁) ++ xs))
... | false = nothing
unifyAcc acc (rightHead ∷ rightTail) with unifyCaseD acc (rightHead ∷ rightTail)
... | just ans = ans
... | nothing with unifyCaseB acc (rightHead ∷ rightTail)
... | just ans = ans
... | nothing = unifyAcc ((rightHead) ∷ acc) rightTail

unifyCaseB acc ((domainExpr (var (just x)) =ℒ domainExpr (var (just y))) ∷ xs) with x ≡ᵇ y
... | true = just (unifyAcc [] (acc ++ xs))
... | false = nothing
unifyCaseB acc ((domainExpr (var (just x)) =ℒ domainExpr (var nothing)) ∷ xs) = just (unifyAcc [] (acc ++ xs))
unifyCaseB acc ((domainExpr (var nothing) =ℒ domainExpr (var (just y))) ∷ xs) = just (unifyAcc [] (acc ++ xs))
unifyCaseB acc ((domainExpr (var nothing) =ℒ domainExpr (var nothing)) ∷ xs) = just (unifyAcc [] (acc ++ xs))
unifyCaseB acc _ = nothing

equalVar : LogicVar (Term LogicVar) → LogicVar (Term LogicVar) → Bool
equalVar (var (just x)) (var (just y)) = x ≡ᵇ y
equalVar _ _ = false

unifyCaseD acc ((domainExpr (var (just x)) =ℒ domainExpr t) ∷ xs) with occursᵥ x (acc ++ xs) ∧ not (equalVar (var (just x)) t)
... | false = nothing
... | true with occursᵥ x t
... | true = just nothing
... | false = just (unifyAcc [] ((applyᵥ x t acc) ++ (domainExpr (var (just x)) =ℒ domainExpr t) ∷ (applyᵥ x t xs)))
unifyCaseD acc ((domainExpr (var nothing) =ℒ domainExpr t) ∷ xs) = nothing
unifyCaseD acc _ = nothing

unify : (right : List (ℒ term)) → Maybe (Subst term)
unify right = unifyAcc [] right