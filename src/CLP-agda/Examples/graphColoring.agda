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

-- a fold to be used for increment later.
foldFunctor = deriveFold functorD

-- Manual FTUtils for Functor.
instance ftUtilsFunctor : FTUtils Functor

         -- functor: textual identifier of the head constructor.
         -- For fnot we keep the inner functor's name so display
         -- like "not nodeColor" can be assembled by the caller
         -- (which checks isNot separately).
         ftUtilsFunctor .functor (fnot x)         = functor ⦃ ftUtilsFunctor ⦄ x
         ftUtilsFunctor .functor (node _)         = "node"
         ftUtilsFunctor .functor (edge _ _)       = "edge"
         ftUtilsFunctor .functor (color _)        = "color"
         ftUtilsFunctor .functor (nodeColor _ _)  = "nodeColor"
         ftUtilsFunctor .functor (otherColor _ _) = "otherColor"
         ftUtilsFunctor .functor ffalse           = "ffalse"

         ftUtilsFunctor .varName _ = nothing

         ftUtilsFunctor .occurs n (fnot x)         = occurs ⦃ ftUtilsFunctor ⦄ n x
         ftUtilsFunctor .occurs n (node a)         = occurs ⦃ ftUtilsString ⦄ n a
         ftUtilsFunctor .occurs n (edge a b)       = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b
         ftUtilsFunctor .occurs n (color a)        = occurs ⦃ ftUtilsString ⦄ n a
         ftUtilsFunctor .occurs n (nodeColor a b)  = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b
         ftUtilsFunctor .occurs n (otherColor a b) = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b
         ftUtilsFunctor .occurs _ ffalse           = false

         ftUtilsFunctor .collectVars (fnot x)         = collectVars ⦃ ftUtilsFunctor ⦄ x
         ftUtilsFunctor .collectVars (node a)         = collectVars ⦃ ftUtilsString ⦄ a
         ftUtilsFunctor .collectVars (edge a b)       = collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b
         ftUtilsFunctor .collectVars (color a)        = collectVars ⦃ ftUtilsString ⦄ a
         ftUtilsFunctor .collectVars (nodeColor a b)  = collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b
         ftUtilsFunctor .collectVars (otherColor a b) = collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b
         ftUtilsFunctor .collectVars ffalse           = []

         ftUtilsFunctor .getNat _ = nothing

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

  graphColoringInstance1 :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  graphColoringInstance1 = do
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

  graphColoringInstance2 :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  graphColoringInstance2 = do
    -- Nodes
    node (~ "a") •
    node (~ "b") •
    node (~ "c") •
    node (~ "d") •
    node (~ "e") •
    node (~ "f") •
    node (~ "g") •
    node (~ "h") •

    -- Edges
    edge (~ "a") (~ "b") •
    edge (~ "a") (~ "c") •
    edge (~ "a") (~ "d") •

    edge (~ "b") (~ "c") •
    edge (~ "b") (~ "e") •

    edge (~ "c") (~ "f") •

    edge (~ "d") (~ "e") •
    edge (~ "d") (~ "f") •

    edge (~ "e") (~ "f") •

    edge (~ "e") (~ "g") •
    edge (~ "f") (~ "h") •

    edge (~ "g") (~ "h") •

  graphColoringInstance3 :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  graphColoringInstance3 = do
    -- Nodes
    node (~ "a") •
    node (~ "b") •
    node (~ "c") •
    node (~ "d") •
    node (~ "e") •
    node (~ "f") •
    node (~ "g") •
    node (~ "h") •
    node (~ "i") •
    node (~ "j") •
    node (~ "k") •
    node (~ "l") •

    -- Clique 1 (a–d)
    edge (~ "a") (~ "b") •
    edge (~ "a") (~ "c") •
    edge (~ "a") (~ "d") •
    edge (~ "b") (~ "c") •
    edge (~ "b") (~ "d") •
    edge (~ "c") (~ "d") •

    -- Clique 2 (e–h)
    edge (~ "e") (~ "f") •
    edge (~ "e") (~ "g") •
    edge (~ "e") (~ "h") •
    edge (~ "f") (~ "g") •
    edge (~ "f") (~ "h") •
    edge (~ "g") (~ "h") •

    -- Clique 3 (i–l)
    edge (~ "i") (~ "j") •
    edge (~ "i") (~ "k") •
    edge (~ "i") (~ "l") •
    edge (~ "j") (~ "k") •
    edge (~ "j") (~ "l") •
    edge (~ "k") (~ "l") •

    -- Interconnections
    edge (~ "a") (~ "e") •
    edge (~ "b") (~ "f") •
    edge (~ "c") (~ "g") •
    edge (~ "d") (~ "h") •

    edge (~ "e") (~ "i") •
    edge (~ "f") (~ "j") •
    edge (~ "g") (~ "k") •
    edge (~ "h") (~ "l") •

    -- Cross links
    edge (~ "b") (~ "g") •
    edge (~ "c") (~ "j") •
    edge (~ "f") (~ "k") •
    edge (~ "d") (~ "i") •

    edge (~ "a") (~ "l") •
    edge (~ "h") (~ "i") •

  graphColoring :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
    → Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  graphColoring inst = do
    inst
    
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

    -- Colors
    color (~ "red") •
    color (~ "green") •
    color (~ "yellow") •

  -- Query: color("a", A).
  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question =
    nodeColor (~ "a") (varString 0) •ₐ

  execute1 = (take 1 ∘ aspExecute (graphColoring graphColoringInstance1) question) (λ { (wrap (nodeColor _ _) _ _) → true ; _ → false })

  execute2 = (take 1 ∘ aspExecute (graphColoring graphColoringInstance2) question) (λ { (wrap (nodeColor _ _) _ _) → true ; _ → false })

  execute3 = (take 1 ∘ aspExecute (graphColoring graphColoringInstance3) question) (λ { (wrap (nodeColor _ _) _ _) → true ; _ → false })

  {-# COMPILE GHC execute1 as gcExecute1 #-}
  
  {-# COMPILE GHC execute2 as gcExecute2 #-}
  
  {-# COMPILE GHC execute3 as gcExecute3 #-}