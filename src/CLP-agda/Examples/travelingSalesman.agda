{-# OPTIONS --rewriting #-}
module Examples.travelingSalesman where

open import Agda.Builtin.Int
open import Data.Bool hiding (_≟_ ; _∧_ ; not)
open import Data.Nat hiding (_≟_)
open import Data.List
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
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  node : StringLogic → Functor
  reachable : StringLogic → Functor
  cycle : StringLogic → StringLogic → Functor
  edge : StringLogic → StringLogic → Functor
  other : StringLogic → StringLogic → Functor
  travelPath : StringLogic → FD → ListLogic (⊎Logic StringLogic (ListLogic FD)) → Functor
  path : StringLogic → StringLogic → StringLogic → FD → ListLogic (⊎Logic StringLogic (ListLogic FD)) → ListLogic (⊎Logic StringLogic (ListLogic FD)) → Functor
  cycleDist : StringLogic → StringLogic → FD → Functor
  distance : StringLogic → StringLogic → FD → Functor
  ffalse  : Functor

functorD : HasDesc Functor
functorD = deriveDesc Functor

-- Manual FTUtils for Functor.
-- The list-element FTUtils dictionary used in travelPath / path.
private
  ftUtilsListElem : FTUtils (⊎Logic StringLogic (ListLogic FD))
  ftUtilsListElem = ftUtils⊎ ⦃ ftUtilsString ⦄ ⦃ ftUtilsList ⦃ ftUtilsFD ⦄ ⦄

  ftUtilsListPath : FTUtils (ListLogic (⊎Logic StringLogic (ListLogic FD)))
  ftUtilsListPath = ftUtilsList ⦃ ftUtilsListElem ⦄

instance ftUtilsFunctor : FTUtils Functor

         ftUtilsFunctor .functor (fnot x)             = functor ⦃ ftUtilsFunctor ⦄ x
         ftUtilsFunctor .functor (node _)             = "node"
         ftUtilsFunctor .functor (reachable _)        = "reachable"
         ftUtilsFunctor .functor (cycle _ _)          = "cycle"
         ftUtilsFunctor .functor (edge _ _)           = "edge"
         ftUtilsFunctor .functor (other _ _)          = "other"
         ftUtilsFunctor .functor (travelPath _ _ _)   = "travelPath"
         ftUtilsFunctor .functor (path _ _ _ _ _ _)   = "path"
         ftUtilsFunctor .functor (cycleDist _ _ _)    = "cycleDist"
         ftUtilsFunctor .functor (distance _ _ _)     = "distance"
         ftUtilsFunctor .functor ffalse               = "ffalse"

         ftUtilsFunctor .varName _ = nothing

         ftUtilsFunctor .occurs n (fnot x)             = occurs ⦃ ftUtilsFunctor ⦄ n x
         ftUtilsFunctor .occurs n (node a)             = occurs ⦃ ftUtilsString ⦄ n a
         ftUtilsFunctor .occurs n (reachable a)        = occurs ⦃ ftUtilsString ⦄ n a
         ftUtilsFunctor .occurs n (cycle a b)          = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b
         ftUtilsFunctor .occurs n (edge a b)           = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b
         ftUtilsFunctor .occurs n (other a b)          = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b
         ftUtilsFunctor .occurs n (travelPath a b c)   = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b ∨ occurs ⦃ ftUtilsListPath ⦄ n c
         ftUtilsFunctor .occurs n (path a b c d e f)   =
           occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b ∨ occurs ⦃ ftUtilsString ⦄ n c ∨
           occurs ⦃ ftUtilsFD ⦄ n d ∨ occurs ⦃ ftUtilsListPath ⦄ n e ∨ occurs ⦃ ftUtilsListPath ⦄ n f
         ftUtilsFunctor .occurs n (cycleDist a b c)    = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b ∨ occurs ⦃ ftUtilsFD ⦄ n c
         ftUtilsFunctor .occurs n (distance a b c)     = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b ∨ occurs ⦃ ftUtilsFD ⦄ n c
         ftUtilsFunctor .occurs _ ffalse               = false

         ftUtilsFunctor .collectVars (fnot x)             = collectVars ⦃ ftUtilsFunctor ⦄ x
         ftUtilsFunctor .collectVars (node a)             = collectVars ⦃ ftUtilsString ⦄ a
         ftUtilsFunctor .collectVars (reachable a)        = collectVars ⦃ ftUtilsString ⦄ a
         ftUtilsFunctor .collectVars (cycle a b)          = collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b
         ftUtilsFunctor .collectVars (edge a b)           = collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b
         ftUtilsFunctor .collectVars (other a b)          = collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b
         ftUtilsFunctor .collectVars (travelPath a b c)   =
           collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b Data.List.++ collectVars ⦃ ftUtilsListPath ⦄ c
         ftUtilsFunctor .collectVars (path a b c d e f)   =
           collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b Data.List.++ collectVars ⦃ ftUtilsString ⦄ c Data.List.++
           collectVars ⦃ ftUtilsFD ⦄ d Data.List.++ collectVars ⦃ ftUtilsListPath ⦄ e Data.List.++ collectVars ⦃ ftUtilsListPath ⦄ f
         ftUtilsFunctor .collectVars (cycleDist a b c)    =
           collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b Data.List.++ collectVars ⦃ ftUtilsFD ⦄ c
         ftUtilsFunctor .collectVars (distance a b c)     =
           collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b Data.List.++ collectVars ⦃ ftUtilsFD ⦄ c
         ftUtilsFunctor .collectVars ffalse               = []

         ftUtilsFunctor .getNat _ = nothing

-- Manual fold for Functor.
foldFunctor :
  ∀ {A : Set}
  → (A → A)                                                                                                                           -- fnot
  → (StringLogic → A)                                                                                                                 -- node
  → (StringLogic → A)                                                                                                                 -- reachable
  → (StringLogic → StringLogic → A)                                                                                                   -- cycle
  → (StringLogic → StringLogic → A)                                                                                                   -- edge
  → (StringLogic → StringLogic → A)                                                                                                   -- other
  → (StringLogic → FD → ListLogic (⊎Logic StringLogic (ListLogic FD)) → A)                                                            -- travelPath
  → (StringLogic → StringLogic → StringLogic → FD → ListLogic (⊎Logic StringLogic (ListLogic FD)) → ListLogic (⊎Logic StringLogic (ListLogic FD)) → A) -- path
  → (StringLogic → StringLogic → FD → A)                                                                                              -- cycleDist
  → (StringLogic → StringLogic → FD → A)                                                                                              -- distance
  → A                                                                                                                                 -- ffalse
  → Functor → A
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (fnot x)             = f₁ (foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ x)
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (node a)             = f₂ a
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (reachable a)        = f₃ a
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (cycle a b)          = f₄ a b
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (edge a b)           = f₅ a b
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (other a b)          = f₆ a b
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (travelPath a b c)   = f₇ a b c
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (path a b c d e f)   = f₈ a b c d e f
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (cycleDist a b c)    = f₉ a b c
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ (distance a b c)     = f₁₀ a b c
foldFunctor f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ ffalse               = f₁₁

-- custom validation scheme, that can be used to restrict the user from certain constructions that would typecheck.
-- in ASP, we could use it to restrict fnot only to be used in the body, and ffalse only in the head.
-- The top type ⊤ would be used for constructions that are allowed, and the bottom type ⊥ for constructions that are illegal.
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

  atomUtils .zipMatch (reachable a) (reachable x) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ [])

  atomUtils .zipMatch (cycle a b) (cycle x y) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (edge a b) (edge x y) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (other a b) (other x y) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (travelPath a b c) (travelPath x y z) =
    just (
      (_:-:_ string𝒞 (a =ℒ x)) ∷
      (_:-:_ fd𝒞 (b =ℒ y)) ∷
      (_:-:_ (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞)))
             (c =ℒ z)
             ⦃ ftUtilsList ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦄) ∷
      [])

  atomUtils .zipMatch (path a b c d p₁ p₂) (path w x y z q₁ q₂) =
    just (
      (_:-:_ string𝒞 (a =ℒ w)) ∷
      (_:-:_ string𝒞 (b =ℒ x)) ∷
      (_:-:_ string𝒞 (c =ℒ y)) ∷
      (_:-:_ fd𝒞 (d =ℒ z)) ∷
      (_:-:_ (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞)))
             (p₁ =ℒ q₁)
             ⦃ ftUtilsList ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦄) ∷
      (_:-:_ (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞)))
             (p₂ =ℒ q₂)
             ⦃ ftUtilsList ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦄) ∷
      [])

  atomUtils .zipMatch (cycleDist a b c) (cycleDist x y z) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷
          (_:-:_ string𝒞 (b =ℒ y)) ∷
          (_:-:_ fd𝒞 (c =ℒ z)) ∷ [])

  atomUtils .zipMatch (distance a b c) (distance x y z) =
    just ((_:-:_ string𝒞 (a =ℒ x)) ∷
          (_:-:_ string𝒞 (b =ℒ y)) ∷
          (_:-:_ fd𝒞 (c =ℒ z)) ∷ [])

  atomUtils .zipMatch ffalse ffalse = just []
  atomUtils .zipMatch _ _ = nothing

  atomUtils .increment n =
    foldFunctor
      fnot
      (λ a → node (incrementString n a))
      (λ a → reachable (incrementString n a))
      (λ a b → cycle (incrementString n a) (incrementString n b))
      (λ a b → edge (incrementString n a) (incrementString n b))
      (λ a b → other (incrementString n a) (incrementString n b))
      (λ a b p → travelPath (incrementString n a)
                            (incrementFD n b)
                            (increment valueUtils (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞))) n p))
      (λ a b c d p₁ p₂ → path (incrementString n a)
                              (incrementString n b)
                              (incrementString n c)
                              (incrementFD n d)
                              (increment valueUtils (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞))) n p₁)
                              (increment valueUtils (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞))) n p₂))
      (λ a b c → cycleDist (incrementString n a)
                           (incrementString n b)
                           (incrementFD n c))
      (λ a b c → distance (incrementString n a)
                          (incrementString n b)
                          (incrementFD n c))
      ffalse
  atomUtils .apply c₀ n z =
    foldFunctor
      fnot
      (λ a → node (apply valueUtils c₀ string𝒞 n z a))
      (λ a → reachable (apply valueUtils c₀ string𝒞 n z a))
      (λ a b → cycle (apply valueUtils c₀ string𝒞 n z a) (apply valueUtils c₀ string𝒞 n z b))
      (λ a b → edge (apply valueUtils c₀ string𝒞 n z a) (apply valueUtils c₀ string𝒞 n z b))
      (λ a b → other (apply valueUtils c₀ string𝒞 n z a) (apply valueUtils c₀ string𝒞 n z b))
      (λ a b p → travelPath (apply valueUtils c₀ string𝒞 n z a)
                            (apply valueUtils c₀ fd𝒞 n z b)
                            (apply valueUtils c₀ (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞))) n z p))
      (λ a b c d p₁ p₂ → path (apply valueUtils c₀ string𝒞 n z a)
                              (apply valueUtils c₀ string𝒞 n z b)
                              (apply valueUtils c₀ string𝒞 n z c)
                              (apply valueUtils c₀ fd𝒞 n z d)
                              (apply valueUtils c₀ (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞))) n z p₁)
                              (apply valueUtils c₀ (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞))) n z p₂))
      (λ a b c → cycleDist (apply valueUtils c₀ string𝒞 n z a)
                           (apply valueUtils c₀ string𝒞 n z b)
                           (apply valueUtils c₀ fd𝒞 n z c))
      (λ a b c → distance (apply valueUtils c₀ string𝒞 n z a)
                          (apply valueUtils c₀ string𝒞 n z b)
                          (apply valueUtils c₀ fd𝒞 n z c))
      ffalse

-- the traveling salesman example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  travelingSalesmanInstance1 :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  travelingSalesmanInstance1 = do
    node (~ "a") •
    node (~ "b") •
    node (~ "c") •
    node (~ "d") •

    distance (~ "b") (~ "c") (＃ (pos 3)) •
    L ← new
    distance (~ "c") (~ "d") L :-
      fd𝒞 ↪ L ＃≥ (＃ (pos 8)) ∧ fd𝒞 ↪ L ＃< (＃ (pos 10)) •
    distance (~ "d") (~ "a") (＃ (pos 1)) •
    distance (~ "a") (~ "b") (＃ (pos 1)) •
    distance (~ "a") (~ "d") (＃ (pos 1)) •
    distance (~ "c") (~ "a") (＃ (pos 1)) •
    distance (~ "d") (~ "b") (＃ (pos 1)) •

  travelingSalesmanInstance2 :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  travelingSalesmanInstance2 = do
    -- Nodes
    node (~ "a") •
    node (~ "b") •
    node (~ "c") •
    node (~ "d") •
    node (~ "e") •
    node (~ "f") •

    -- Distances
    distance (~ "a") (~ "b") (＃ (pos 2)) •

    L1 ← new
    distance (~ "b") (~ "c") L1 :-
      fd𝒞 ↪ L1 ＃> (＃ (pos 3)) ∧ fd𝒞 ↪ L1 ＃< (＃ (pos 6)) •

    distance (~ "c") (~ "d") (＃ (pos 4)) •

    L2 ← new
    distance (~ "d") (~ "e") L2 :-
      fd𝒞 ↪ L2 ＃≥ (＃ (pos 2)) ∧ fd𝒞 ↪ L2 ＃≤ (＃ (pos 5)) •

    distance (~ "e") (~ "f") (＃ (pos 3)) •
    distance (~ "f") (~ "a") (＃ (pos 2)) •

    -- Cross connections
    distance (~ "a") (~ "c") (＃ (pos 5)) •
    distance (~ "b") (~ "d") (＃ (pos 6)) •

    L3 ← new
    distance (~ "c") (~ "e") L3 :-
      fd𝒞 ↪ L3 ＃> (＃ (pos 1)) ∧ fd𝒞 ↪ L3 ＃< (＃ (pos 4)) •

    distance (~ "d") (~ "f") (＃ (pos 4)) •
    distance (~ "e") (~ "a") (＃ (pos 7)) •

    L4 ← new
    distance (~ "f") (~ "b") L4 :-
      fd𝒞 ↪ L4 ＃≥ (＃ (pos 3)) ∧ fd𝒞 ↪ L4 ＃≤ (＃ (pos 6)) •  

  travelingSalesmanInstance3 :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  travelingSalesmanInstance3 = do
    -- Nodes
    node (~ "a") •
    node (~ "b") •
    node (~ "c") •
    node (~ "d") •
    node (~ "e") •
    node (~ "f") •
    node (~ "g") •
    node (~ "h") •

    -- Base cycle
    distance (~ "a") (~ "b") (＃ (pos 2)) •

    L1 ← new
    distance (~ "b") (~ "c") L1 :-
      fd𝒞 ↪ L1 ＃> (＃ (pos 2)) ∧ fd𝒞 ↪ L1 ＃< (＃ (pos 7)) •

    distance (~ "c") (~ "d") (＃ (pos 3)) •

    L2 ← new
    distance (~ "d") (~ "e") L2 :-
      fd𝒞 ↪ L2 ＃≥ (＃ (pos 4)) ∧ fd𝒞 ↪ L2 ＃≤ (＃ (pos 8)) •

    distance (~ "e") (~ "f") (＃ (pos 2)) •

    L3 ← new
    distance (~ "f") (~ "g") L3 :-
      fd𝒞 ↪ L3 ＃> (＃ (pos 1)) ∧ fd𝒞 ↪ L3 ＃< (＃ (pos 5)) •

    distance (~ "g") (~ "h") (＃ (pos 3)) •

    L4 ← new
    distance (~ "h") (~ "a") L4 :-
      fd𝒞 ↪ L4 ＃≥ (＃ (pos 2)) ∧ fd𝒞 ↪ L4 ＃≤ (＃ (pos 6)) •

    -- Dense cross connections
    distance (~ "a") (~ "c") (＃ (pos 6)) •

    L5 ← new
    distance (~ "a") (~ "d") L5 :-
      fd𝒞 ↪ L5 ＃> (＃ (pos 5)) ∧ fd𝒞 ↪ L5 ＃< (＃ (pos 10)) •

    distance (~ "b") (~ "d") (＃ (pos 4)) •

    L6 ← new
    distance (~ "b") (~ "e") L6 :-
      fd𝒞 ↪ L6 ＃≥ (＃ (pos 3)) ∧ fd𝒞 ↪ L6 ＃≤ (＃ (pos 7)) •

    distance (~ "c") (~ "e") (＃ (pos 5)) •

    L7 ← new
    distance (~ "c") (~ "f") L7 :-
      fd𝒞 ↪ L7 ＃> (＃ (pos 2)) ∧ fd𝒞 ↪ L7 ＃< (＃ (pos 6)) •

    distance (~ "d") (~ "f") (＃ (pos 3)) •

    L8 ← new
    distance (~ "d") (~ "g") L8 :-
      fd𝒞 ↪ L8 ＃≥ (＃ (pos 4)) ∧ fd𝒞 ↪ L8 ＃≤ (＃ (pos 9)) •

    distance (~ "e") (~ "g") (＃ (pos 4)) •

    L9 ← new
    distance (~ "e") (~ "h") L9 :-
      fd𝒞 ↪ L9 ＃> (＃ (pos 3)) ∧ fd𝒞 ↪ L9 ＃< (＃ (pos 8)) •

    distance (~ "f") (~ "h") (＃ (pos 5)) •

    L10 ← new
    distance (~ "g") (~ "a") L10 :-
      fd𝒞 ↪ L10 ＃≥ (＃ (pos 6)) ∧ fd𝒞 ↪ L10 ＃≤ (＃ (pos 10)) •

  travelingSalesma :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
    → Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  travelingSalesma inst = do
    inst

    U ← new

    ffalse :- node U ∧ₐ not (reachable U) •ₐ

    V ← new
    reachable (~ "a") :- cycle V (~ "a") •ₐ
    reachable V :-
      cycle U V ∧ₐ
      reachable U •ₐ

    W ← new
    ffalse :- cycle U W ∧ₐ cycle V W ∧ₐ string𝒞 ↣ U ≠ℒ V •

    cycle U V :-
      edge U V ∧ₐ not (other U V) •ₐ
    other U V :-
      node U ∧ₐ node V ∧ₐ node W ∧ₐ
      edge U W ∧ₐ string𝒞 ↣ V ≠ℒ W ∧ cycle U W •ₐ
    
    S ← new
    Ln ← new
    Cycle ← new
    A ← new
    X ← new
    Y ← new
    Z ← new
    D ← new
    D1 ← new
    D2 ← new
    Ps ← new
    Cs ← new
    travelPath S Ln Cycle :-
      path S S S Ln [] Cycle •ₐ
    path A X Y D Ps ((p X) ∷ (q (D ∷ [])) ∷ (p Y) ∷ Ps) :-
      cycleDist X Y D •ₐ
    path S X Y D Ps Cs :-
      fd𝒞 ↣ D =ℒ D1 ＃+ D2 ∧
      cycleDist Z Y D1 ∧ₐ string𝒞 ↣ Z ≠ℒ S ∧
      path S X Z D2 ((q (D1 ∷ [])) ∷ (p Y) ∷ Ps) Cs •ₐ
    
    edge X Y :- distance X Y D •ₐ
    cycleDist U V D :-
      cycle U V ∧ₐ distance U V D •ₐ

  question :
    ℕ
    → Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question n = 
    fd𝒞 ↪ (varFD 0) ＃< (＃ (pos n)) ∧ fd𝒞 ↪ (varFD 0) ＃≥ (＃ (pos 0)) ∧ travelPath (~ "b") (varFD 0) (varList 1) •ₐ

  execute1 = (take 1 ∘ aspExecute (travelingSalesma travelingSalesmanInstance1) (question 10)) (λ { (wrap (travelPath _ _ _) _ _) → true ; _ → false })

  execute2 = (take 1 ∘ aspExecute (travelingSalesma travelingSalesmanInstance2) (question 30)) (λ { (wrap (travelPath _ _ _) _ _) → true ; _ → false })

  execute3 = (take 1 ∘ aspExecute (travelingSalesma travelingSalesmanInstance3) (question 30)) (λ { (wrap (travelPath _ _ _) _ _) → true ; _ → false })

  {-# COMPILE GHC execute1 as tsExecute1 #-}
  
  {-# COMPILE GHC execute2 as tsExecute2 #-}
  
  {-# COMPILE GHC execute3 as tsExecute3 #-}