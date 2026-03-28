module Examples.nQueens where

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
open import Product.domain
open import List.domain

open import ASP.types
open import ASP.asp
open import ASP.dual

open import Examples.myDomainGroup

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  nqueens : FD → ListLogic (×Logic FD FD) → Functor
  nqueens₀ : FD → FD → ListLogic (×Logic FD FD) → ListLogic (×Logic FD FD) → Functor
  pickqueen : FD → FD → FD → Functor
  qf : FD → FD → Functor
  negqf : FD → FD → Functor
  attack : FD → FD → ListLogic (×Logic FD FD) → Functor
  abs : FD → FD → Functor
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
instance  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch (fnot x) (fnot y) = zipMatch atomUtils x y
          atomUtils .zipMatch (nqueens a b) (nqueens x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (list𝒞 (×𝒞 FD𝒞 FD𝒞)) (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (nqueens₀ a b c d) (nqueens₀ x y z e) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ 
                  (_:-:_ (list𝒞 (×𝒞 FD𝒞 FD𝒞)) (c =ℒ z)) ∷ (_:-:_ (list𝒞 (×𝒞 FD𝒞 FD𝒞)) (d =ℒ e)) ∷ [])
          atomUtils .zipMatch (pickqueen a b c) (pickqueen x y z) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ (_:-:_ FD𝒞 (c =ℒ z)) ∷ [])
          atomUtils .zipMatch (qf a b) (qf x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (negqf a b) (negqf x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (attack a b c) (attack x y z) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ (_:-:_ (list𝒞 (×𝒞 FD𝒞 FD𝒞)) (c =ℒ z)) ∷ [])
          atomUtils .zipMatch (abs a b) (abs x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a b → nqueens (incrementFD n a) (increment valueUtils (list𝒞 (×𝒞 FD𝒞 FD𝒞)) n b))
              (λ a b c d → nqueens₀ (incrementFD n a) (incrementFD n b) (increment valueUtils (list𝒞 (×𝒞 FD𝒞 FD𝒞)) n c) (increment valueUtils (list𝒞 (×𝒞 FD𝒞 FD𝒞)) n d))
              (λ a b c → pickqueen (incrementFD n a) (incrementFD n b) (incrementFD n c))
              (λ a b → qf (incrementFD n a) (incrementFD n b))
              (λ a b → negqf (incrementFD n a) (incrementFD n b))
              (λ a b c → attack (incrementFD n a) (incrementFD n b) (increment valueUtils (list𝒞 (×𝒞 FD𝒞 FD𝒞)) n c))
              (λ a b → abs (incrementFD n a) (incrementFD n b))
              ffalse

-- the streamreasoning example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  nQueens :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  nQueens = do
    N ← new
    Q ← new

    nqueens N Q :-
      nqueens₀ N N [] Q •ₐ
    
    X ← new
    Y ← new
    X1 ← new
    Qi ← new
    Qo ← new

    nqueens₀ X N Qi Qo :-
      FD𝒞 ↪ X ＃> ＃ (pos 0) ∧
      pickqueen X Y N ∧ₐ
      not (attack X Y Qi) ∧ₐ
      FD𝒞 ↣ X1 =ℒ X ＃- ＃ (pos 1) ∧
      nqueens₀ X1 N ((X ∶ Y) ∷ Qi) Qo •ₐ
    nqueens₀ (＃ (pos 0)) N Q Q •
    
    N1 ← new

    pickqueen X Y Y :-
      FD𝒞 ↪ Y ＃> ＃ (pos 0) ∧
      qf X Y •ₐ
    pickqueen X Y N :-
      FD𝒞 ↪ N ＃> ＃ (pos 1) ∧
      FD𝒞 ↣ N1 =ℒ N ＃- ＃ (pos 1) ∧
      pickqueen X Y N1 •ₐ
    
    A ← new
    B ← new
    C ← new
    X2 ← new
    Y2 ← new
    Xd ← new
    Yd ← new
    Xd2 ← new
    Yd2 ← new

    attack X A ((X ∶ B) ∷ C) •
    attack A Y ((B ∶ Y) ∷ C) •
    attack X Y ((X2 ∶ Y2) ∷ C) :-
      FD𝒞 ↣ Xd =ℒ X2 ＃- X ∧
      abs Xd Xd2 ∧ₐ
      FD𝒞 ↣ Yd =ℒ Y2 ＃- Y ∧
      abs Yd Yd2 ∧ₐ
      FD𝒞 ↣ Xd2 =ℒ Yd2 •
    A ← new
    T ← new
    attack X Y (A ∷ T) :-
      attack X Y T •ₐ
    
    qf X Y :- not (negqf X Y) •ₐ
    negqf X Y :- not (qf X Y) •ₐ

    abs X X :- FD𝒞 ↪ X ＃≥ ＃ (pos 0) •
    abs X Y :- FD𝒞 ↪ X ＃< ＃ (pos 0) ∧ FD𝒞 ↣ Y =ℒ X ＃* ＃ (negsuc 0) •

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    nqueens (＃ (pos 4)) (varList 0) •ₐ

  execute = (head ∘ aspExecute nQueens) question

  getDuals = computeDuals (toIntern nQueens)