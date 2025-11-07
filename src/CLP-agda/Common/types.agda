module Common.types where

open import Term.types
open import Data.Maybe 
  using (Maybe)
open import Data.Nat 
  using (ℕ)
open import Data.List 
  using (List)
open import Data.Product 
  using (_×_)
open import Data.Nat 
  using (ℕ)
open import Data.String 
  using (String)

-- Type interjecting the extensive domain type with choice between var and provided value.
data LogicVar (a : Set) : Set where
  var : Maybe ℕ → LogicVar a
  const : a → LogicVar a

-- Codes for generic domain universe.
data 𝒞 : Set where
  term : 𝒞
-- real : 𝒞

-- Decode function for domain universe.
⟦_⟧₍𝑑₎ : 𝒞 → (Set → Set) → Set
⟦ term ⟧₍𝑑₎ = Term
-- ⟦ real ⟧₍𝑑₎ = Real

-- Abstract expression type. Term doesn't have any function symbols so there are no composites by now.
-- Extensive domain type extended by LogicVar.
data Expr : 𝒞 → Set where
  domainExpr : {c : 𝒞} → LogicVar (⟦ c ⟧₍𝑑₎ LogicVar) → Expr c
-- _+_ : Expr real → Expr real → Expr real
-- _-_ : Expr real → Expr real → Expr real
-- _*_ : Expr real → Expr real → Expr real
-- _/_ : Expr real → Expr real → Expr real

-- Abstract domain constraint type. Every domain has constraints =ℒ and ≠ℒ, Term has no additional ones.
data ℒ : 𝒞 → Set where
  _=ℒ_ : {c : 𝒞} → Expr c → Expr c → ℒ c
  _≠ℒ_ : {c : 𝒞} → Expr c → Expr c → ℒ c
-- _≤ℒ_ : Expr real → Expr real → ℒ real
-- _≥ℒ_ : Expr real → Expr real → ℒ real
-- _<ℒ_ : Expr real → Expr real → ℒ real
-- _>ℒ_ : Expr real → Expr real → ℒ real

record Atom (c : 𝒞) : Set where
  constructor mkAtom
  field
    functor : String
    args : List (Expr c)

data Literal (c : 𝒞) : Set where
  atomLiteral : Atom c → Literal c
  𝓁Literal    : ℒ c → Literal c

-- Clause type. Either rule or fact. 
-- If the list in the second argument is empty, it is a fact.
-- (empty rules and facts are semantically the same, the special syntax for facts is only sugar).
record Clause (c : 𝒞) : Set where
  constructor _:-_
  field 
    head : Atom c
    body : List (Literal c)

-- Generic type for Substitutions (Output of the solver).
-- Extensive domain type extended by LogicVar.
Subst : 𝒞 → Set
Subst c = List (ℕ × (LogicVar (⟦ c ⟧₍𝑑₎ LogicVar)))

-- Generic universe codes for entities that have variables.
-- Extensively used by the utilities.
data HasVariables : Set where
  expr     : (c : 𝒞) → HasVariables
  domainConstraint   : (c : 𝒞) → HasVariables
  atom        : (c : 𝒞) → HasVariables
  literal     : (c : 𝒞) → HasVariables
  clause      : (c : 𝒞) → HasVariables
  listOf      : HasVariables → HasVariables
  domainExpr    : (c : 𝒞) → HasVariables

-- Decoding function for HasVariables
⟦_⟧ᵥ : HasVariables → Set
⟦ expr c ⟧ᵥ   = Expr c
⟦ domainConstraint c ⟧ᵥ = ℒ c
⟦ atom c ⟧ᵥ      = Atom c
⟦ literal c ⟧ᵥ   = Literal c
⟦ clause c ⟧ᵥ    = Clause c
⟦ listOf c ⟧ᵥ    = List (⟦ c ⟧ᵥ)
⟦ domainExpr c ⟧ᵥ  = LogicVar (⟦ c ⟧₍𝑑₎ LogicVar)