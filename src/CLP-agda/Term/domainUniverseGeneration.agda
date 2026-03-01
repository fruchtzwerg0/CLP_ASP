{-# OPTIONS --safe #-}

module Term.domainUniverseGeneration where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Data.Bool
open import Data.List
open import Data.Product hiding (map)

_>>=_ : {A B : Set} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ : {A B : Set} → TC A → TC B → TC B
m >> n = bindTC m (λ _ → n)

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

mapTC : {A B : Set} → (A → TC B) → List A → TC (List B)
mapTC f []       = returnTC []
mapTC f (x ∷ xs) = do
  y  ← f x
  ys ← mapTC f xs
  returnTC (y ∷ ys)

------------------------------------------------------------------------
-- Extract parameter count and constructors
------------------------------------------------------------------------
isData : Definition → Bool
isData (data-type _ _) = true
isData _               = false

dataPars : Definition → Nat
dataPars (data-type pars _) = pars
dataPars _                   = 0

getInductiveArity : Name → TC Nat
getInductiveArity n = do
  defi ← getDefinition n
  returnTC (if isData defi then dataPars defi else 0)

makeConstructor : Name → Nat → Name → TC (Σ Name (λ _ → Type))
makeConstructor n arity myCName = do
  let args = replicate arity (arg (arg-info visible (modality relevant quantity-ω)) (con myCName []))
  returnTC (n , foldr (λ a t → pi a (abs "_" t)) (con myCName []) args)

makeUniverse : List Name → TC ⊤
makeUniverse typeNames = do
  myCName ← freshName "My𝒞"

  -- Make constructors
  cons ← mapTC (λ n → do
                  arity ← getInductiveArity n
                  makeConstructor n arity myCName) typeNames

  -- Declare the data type
  declareData myCName 0 (agda-sort (set (lit (nat 0))))  -- My𝒞 : Set
  defineData myCName cons