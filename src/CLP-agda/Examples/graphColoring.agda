{-# OPTIONS --rewriting #-}
module Examples.graphColoring where

open import Agda.Builtin.Int
open import Data.Bool hiding (_≟_ ; _∧_ ; not)
open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.String
open import Data.Sum
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Function.Base

open import Generics

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import CLP.ftUtilsDerivation
open import CLP.types
open import CLP.unifyDisunify
open import CLP.solverScheduler
open import CLP.clp
open import Empty.domain
open import Bool.domain
open import FD.domain
open import Sum.domain
open import List.domain
open import String.domain

open import ASP.types
open import ASP.asp
open import ASP.dual
open import ASP.nmr
open import ASP.loops

open import Examples.myDomainGroup

open import CLP.utilities

-- "types" of atoms to be used by the logic program
-- Both nodes and colors are strings now.
data Functor : Set where
  fnot       : Functor → Functor
  node       : StringLogic → Functor
  edge       : StringLogic → StringLogic → Functor
  color      : StringLogic → Functor
  nodeColor  : StringLogic → StringLogic → Functor
  otherColor : StringLogic → StringLogic → Functor
  ffalse     : Functor

functorD : HasDesc Functor
functorD = deriveDesc Functor

-- we need to derive ftUtils for our atom type
instance  ftUtilsFunctor : FTUtils Functor
          ftUtilsFunctor = deriveFTUtils functorD

-- a fold to be used for increment later.
foldFunctor = deriveFold functorD

-- custom validation scheme
validate : Where → Functor → Set
validate _ (fnot _) = ⊤
validate _ ffalse = ⊤
validate _ _ = ⊤

-- We only need to provide this if we use ASP.
instance  aspUtils : ASPUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          aspUtils .not = fnot
          aspUtils .isNot (fnot _) = true
          aspUtils .isNot _ = false
          aspUtils .isFalse ffalse = true
          aspUtils .isFalse _ = false
          aspUtils .toggle (fnot x) = x
          aspUtils .toggle x = fnot x

instance showFunctor : Show Functor
         showFunctor = deriveShow functorD

-- These are general functions that we need in the generic CLP scheme.
instance
  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
  atomUtils .zipMatch (fnot x) (fnot y) =
    zipMatch atomUtils x y

  atomUtils .zipMatch (node a) (node x) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ [])

  atomUtils .zipMatch (edge a b) (edge x y) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (color a) (color x) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ [])

  atomUtils .zipMatch (nodeColor a b) (nodeColor x y) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (otherColor a b) (otherColor x y) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch ffalse ffalse = just []
  atomUtils .zipMatch _ _ = nothing

  atomUtils .increment n =
    foldFunctor
      fnot
      (λ a → node (incrementString n a))
      (λ a b → edge (incrementString n a) (incrementString n b))
      (λ a → color (incrementString n a))
      (λ a b → nodeColor (incrementString n a) (incrementString n b))
      (λ a b → otherColor (incrementString n a) (incrementString n b))
      ffalse
  atomUtils .apply c₀ n z =
    foldFunctor
      fnot
      (λ a → node (apply valueUtils c₀ string𝒞 n z a))
      (λ a b → edge (apply valueUtils c₀ string𝒞 n z a)
                    (apply valueUtils c₀ string𝒞 n z b))
      (λ a → color (apply valueUtils c₀ string𝒞 n z a))
      (λ a b → nodeColor (apply valueUtils c₀ string𝒞 n z a)
                         (apply valueUtils c₀ string𝒞 n z b))
      (λ a b → otherColor (apply valueUtils c₀ string𝒞 n z a)
                          (apply valueUtils c₀ string𝒞 n z b))
      ffalse

module program where
  open CLP.types

  graphColoring :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  graphColoring = do
    X ← new
    C ← new
    C2 ← new

    otherColor X C :-
      color C ∧ₐ color C2 ∧ₐ
      string𝒞 ↣ C ≠ℒ C2 ∧
      nodeColor X C2 •ₐ

    nodeColor X C :-
      node X ∧ₐ color C ∧ₐ not (otherColor X C) •ₐ

    Y ← new
    ffalse :-
      edge X Y ∧ₐ
      nodeColor X C ∧ₐ
      nodeColor Y C •ₐ

    -- Nodes
    node (~ "a") •
    node (~ "b") •
    node (~ "c") •
    node (~ "d") •
    node (~ "e") •

    -- Edges
    edge (~ "a") (~ "b") •
    edge (~ "a") (~ "c") •
    edge (~ "b") (~ "d") •
    edge (~ "b") (~ "e") •
    edge (~ "c") (~ "d") •
    edge (~ "c") (~ "e") •

    -- Colors
    color (~ "red") •
    color (~ "green") •
    color (~ "yellow") •

  -- Query: color("a", A).
  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question =
    nodeColor (~ "a") (varString 0) •ₐ
  questionTest :
    List (Literal (ASPAtom Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ) My𝒞 ⟦_⟧ ⟦_⟧ℒ)
  questionTest =
    atom (wrap (not (otherColor (~ "a") (varString 0))) 1 ((string𝒞 :-: (~ "a")) ∷ (string𝒞 :-: varString 0) ∷ (string𝒞 :-: varString 1) ∷ [])) ∷ []

  realColoring = (toIntern ∘ proj₂ ∘ applyVars graphColoring) 0

  execute = (take 1 ∘ aspExecute graphColoring question) (λ { (wrap (nodeColor _ _) _ _) → true ; _ → false })

  fExecute = (take 5 ∘ aspExecuteDirect graphColoring questionTest) (λ { (wrap (nodeColor _ _) _ _) → true ; _ → false })

  {-# COMPILE GHC execute as execute #-}

  real = (toIntern  ∘ proj₂ ∘ applyVars graphColoring) 0
  getDuals = computeDuals real
  getNmr = computeNMR real
  getOlon = findOLON real