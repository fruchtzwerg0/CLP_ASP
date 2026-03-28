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

open import ASP.types
open import ASP.asp
open import ASP.dual
open import ASP.nmr

open import Examples.myDomainGroup

open import CLP.utilities

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  node : FD → Functor
  reachable : FD → Functor
  cycle : FD → FD → Functor
  edge : FD → FD → Functor
  other : FD → FD → Functor
  travelPath : FD → FD → ListLogic (⊎Logic FD (ListLogic FD)) → Functor
  path : FD → FD → FD → FD → ListLogic (⊎Logic FD (ListLogic FD)) → ListLogic (⊎Logic FD (ListLogic FD)) → Functor
  cycleDist : FD → FD → FD → Functor
  distance : FD → FD → FD → Functor
  ffalse  : Functor

functorD : HasDesc Functor
functorD = deriveDesc Functor

-- we need to derive ftUtils for our atom type
instance  ftUtilsFunctor : FTUtils Functor
          ftUtilsFunctor = deriveFTUtils functorD

-- a fold to be used for increment later.
foldFunctor = deriveFold functorD

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

-- These are general functions that we need in the generic CLP scheme.
instance
  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
  atomUtils .zipMatch (fnot x) (fnot y) =
    zipMatch atomUtils x y

  atomUtils .zipMatch (node a) (node x) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ [])

  atomUtils .zipMatch (reachable a) (reachable x) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ [])

  atomUtils .zipMatch (cycle a b) (cycle x y) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (edge a b) (edge x y) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (other a b) (other x y) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])

  atomUtils .zipMatch (travelPath a b c) (travelPath x y z) =
    just (
      (_:-:_ FD𝒞 (a =ℒ x)) ∷
      (_:-:_ FD𝒞 (b =ℒ y)) ∷
      (_:-:_ (list𝒞 (⊎𝒞 FD𝒞 (list𝒞 FD𝒞)))
             (c =ℒ z)
             ⦃ ftUtilsList ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦄) ∷
      [])

  atomUtils .zipMatch (path a b c d p₁ p₂) (path w x y z q₁ q₂) =
    just (
      (_:-:_ FD𝒞 (a =ℒ w)) ∷
      (_:-:_ FD𝒞 (b =ℒ x)) ∷
      (_:-:_ FD𝒞 (c =ℒ y)) ∷
      (_:-:_ FD𝒞 (d =ℒ z)) ∷
      (_:-:_ (list𝒞 (⊎𝒞 FD𝒞 (list𝒞 FD𝒞)))
             (p₁ =ℒ q₁)
             ⦃ ftUtilsList ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦄) ∷
      (_:-:_ (list𝒞 (⊎𝒞 FD𝒞 (list𝒞 FD𝒞)))
             (p₂ =ℒ q₂)
             ⦃ ftUtilsList ⦄ ⦃ ftUtils⊥ ⦄ ⦃ decList ⦄) ∷
      [])

  atomUtils .zipMatch (cycleDist a b c) (cycleDist x y z) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷
          (_:-:_ FD𝒞 (b =ℒ y)) ∷
          (_:-:_ FD𝒞 (c =ℒ z)) ∷ [])

  atomUtils .zipMatch (distance a b c) (distance x y z) =
    just ((_:-:_ FD𝒞 (a =ℒ x)) ∷
          (_:-:_ FD𝒞 (b =ℒ y)) ∷
          (_:-:_ FD𝒞 (c =ℒ z)) ∷ [])

  atomUtils .zipMatch ffalse ffalse = just []
  atomUtils .zipMatch _ _ = nothing

  atomUtils .increment n =
    foldFunctor
      fnot
      (λ a → node (incrementFD n a))
      (λ a → reachable (incrementFD n a))
      (λ a b → cycle (incrementFD n a) (incrementFD n b))
      (λ a b → edge (incrementFD n a) (incrementFD n b))
      (λ a b → other (incrementFD n a) (incrementFD n b))
      (λ a b p → travelPath (incrementFD n a)
                            (incrementFD n b)
                            (increment valueUtils (list𝒞 (⊎𝒞 FD𝒞 (list𝒞 FD𝒞))) n p))
      (λ a b c d p₁ p₂ → path (incrementFD n a)
                              (incrementFD n b)
                              (incrementFD n c)
                              (incrementFD n d)
                              (increment valueUtils (list𝒞 (⊎𝒞 FD𝒞 (list𝒞 FD𝒞))) n p₁)
                              (increment valueUtils (list𝒞 (⊎𝒞 FD𝒞 (list𝒞 FD𝒞))) n p₂))
      (λ a b c → cycleDist (incrementFD n a)
                           (incrementFD n b)
                           (incrementFD n c))
      (λ a b c → distance (incrementFD n a)
                          (incrementFD n b)
                          (incrementFD n c))
      ffalse

-- the streamreasoning example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  travelingSalesma :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  travelingSalesma = do
    U ← new

    ffalse :- node U ∧ₐ not (reachable U) •ₐ

    V ← new
    reachable (＃ (pos 0)) :- cycle V (＃ (pos 0)) •ₐ
    reachable V :-
      cycle U V ∧ₐ
      reachable U •ₐ

    W ← new
    ffalse :- cycle U W ∧ₐ cycle V W ∧ₐ FD𝒞 ↣ U ≠ℒ V •

    cycle U V :-
      edge U V ∧ₐ not (other U V) •ₐ
    other U V :-
      node U ∧ₐ node V ∧ₐ node W ∧ₐ
      edge U W ∧ₐ FD𝒞 ↣ V ≠ℒ W ∧ cycle U W •ₐ
    
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
      FD𝒞 ↣ D =ℒ D1 ＃+ D2 ∧
      cycleDist Z Y D1 ∧ₐ FD𝒞 ↣ Z ≠ℒ S ∧
      path S X Z D2 ((q (D1 ∷ [])) ∷ (p Y) ∷ Ps) Cs •ₐ
    
    edge X Y :- distance X Y D •ₐ
    cycleDist U V D :-
      cycle U V ∧ₐ distance U V D •ₐ
    
    node (＃ (pos 0)) •
    node (＃ (pos 1)) •
    node (＃ (pos 2)) •
    node (＃ (pos 3)) •

    distance (＃ (pos 1)) (＃ (pos 2)) (＃ (pos 3)) •
    L ← new
    distance (＃ (pos 2)) (＃ (pos 3)) L :-
      FD𝒞 ↪ L ＃≥ (＃ (pos 8)) ∧ FD𝒞 ↪ L ＃< (＃ (pos 10)) •
    distance (＃ (pos 3)) (＃ (pos 0)) (＃ (pos 1)) •
    distance (＃ (pos 0)) (＃ (pos 1)) (＃ (pos 1)) •
    distance (＃ (pos 0)) (＃ (pos 3)) (＃ (pos 1)) •
    distance (＃ (pos 2)) (＃ (pos 0)) (＃ (pos 1)) •
    distance (＃ (pos 3)) (＃ (pos 2)) (＃ (pos 1)) •

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    FD𝒞 ↪ (varFD 0) ＃< (＃ (pos 10)) ∧ travelPath (＃ (pos 1)) (varFD 0) (varList 1) •ₐ
    
  realTravel = (toIntern ∘ proj₂ ∘ applyVars travelingSalesma) 0

  getNmr = computeNMR realTravel
  getNmra = findOLON ((cycle (varFD 0) (varFD 1) :--
        (atom (edge (varFD 0) (varFD 1)) ∷
        atom (fnot (other (varFD 0) (varFD 1))) ∷ []))
        ∷
        (other (varFD 0) (varFD 1) :--
        (atom (node (varFD 0)) ∷
        atom (node (varFD 1)) ∷
        atom (node (varFD 2)) ∷
        atom (edge (varFD 0) (varFD 2)) ∷
        constraint (inj₁ (FD𝒞 :-: (varFD 1 ≠ℒ varFD 2))) ∷
        atom (cycle (varFD 0) (varFD 2)) ∷ []))
        ∷ [])
  adj = getAdjacent ((cycle (varFD 0) (varFD 1) :--
        (atom (edge (varFD 0) (varFD 1)) ∷
        atom (fnot (other (varFD 0) (varFD 1))) ∷ []))
        ∷
        (other (varFD 0) (varFD 1) :--
        (atom (node (varFD 0)) ∷
        atom (node (varFD 1)) ∷
        atom (node (varFD 2)) ∷
        atom (edge (varFD 0) (varFD 2)) ∷
        constraint (inj₁ (FD𝒞 :-: (varFD 1 ≠ℒ varFD 2))) ∷
        atom (cycle (varFD 0) (varFD 2)) ∷ []))
        ∷ []) (cycle (varFD 0) (varFD 1) , 0)
  getOlon = findOLON realTravel