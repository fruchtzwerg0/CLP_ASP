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

-- the streamreasoning example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  travelingSalesma :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  travelingSalesma = do
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

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    fd𝒞 ↪ (varFD 0) ＃< (＃ (pos 10)) ∧ fd𝒞 ↪ (varFD 0) ＃≥ (＃ (pos 0)) ∧ travelPath (~ "b") (varFD 0) (varList 1) •ₐ
  realTravel = (toIntern ∘ proj₂ ∘ applyVars travelingSalesma) 0
  {-

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
        constraint (inj₁ (fd𝒞 :-: (varFD 1 ≠ℒ varFD 2))) ∷
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
        constraint (inj₁ (fd𝒞 :-: (varFD 1 ≠ℒ varFD 2))) ∷
        atom (cycle (varFD 0) (varFD 2)) ∷ []))
        ∷ []) (cycle (varFD 0) (varFD 1) , 0)
  getOlon = findOLON realTravel
  -}
  execute = (take 1 ∘ aspExecute travelingSalesma question) (λ { (wrap (travelPath _ _ _) _ _) → true ; _ → false })

  
  {-# COMPILE GHC execute as execute #-}
  
  result = unifyDisunify (list𝒞 fd𝒞) (λ _ _ → false) (λ _ _ x → x) (inj₁ (varList 151 =ℒ varList 1) ∷ []) (inj₁ (varList 1 =ℒ (varFD 19 ∷ [])) ∷ []) tt
  result2 = unifyDisunify (list𝒞 fd𝒞) 
              (λ _ _ → false) (λ _ _ x → x) 
              (inj₁ (varList 21 =ℒ []) ∷ []) 
              (inj₁ (varList 21 =ℒ varList 50) ∷ []) 
              tt
  result3 = unifyDisunify (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞)))
    (λ _ _ → false) (λ _ _ x → x) 
    []                                                  -- normalized: empty
    (inj₁ (varList 13 =ℒ varList 25) ∷                 -- new: 5th arg unification
    inj₁ (varList 14 =ℒ 
            (p (varString 22) ∷ 
            q (varFD 24 ∷ []) ∷ 
            p (varString 23) ∷ 
            varList 25)) ∷                             -- new: 6th arg unification
    []) 
    tt

  asdf = bindAndRename (path (varString 100) (varString 101) (varString 102) (varFD 103) (varList 104) (varList 105)) 105
            ((path (varString 3) (varString 7) (varString 8) (varFD 10)
                (varList 13) (varList 14)
                :--
                (constraint (inj₁ (fd𝒞 :-: (varFD 10 =ℒ varFD 11 ＃+ varFD 12))) ∷
                  atom (cycleDist (varString 9) (varString 8) (varFD 11)) ∷
                  constraint (inj₁ (string𝒞 :-: (varString 9 ≠ℒ varString 3))) ∷
                  atom
                  (path (varString 3) (varString 7) (varString 9) (varFD 12)
                  (q (varFD 11 ∷ []) ∷ (p (varString 8) ∷ varList 13)) (varList 14))
                  ∷ [])))
  test = unifyDisunify (list𝒞 (⊎𝒞 string𝒞 (list𝒞 fd𝒞)))
    (λ _ _ → false) (λ _ _ x → x)
    -- normalized: simulate the store before base case
    (inj₁ (varList 151 =ℒ varList 1) ∷ 
    inj₁ (varList 108 =ℒ varList 1) ∷ 
    inj₁ (varList 21 =ℒ []) ∷ 
    [])
    -- new: simulate base case's 6th arg unification
    (inj₁ (varList 151 =ℒ ((p (varString 200)) ∷ 
                            (q (varFD 201 ∷ [])) ∷ 
                            (p (varString 202)) ∷ 
                            varList 21)) ∷ 
    [])
    tt