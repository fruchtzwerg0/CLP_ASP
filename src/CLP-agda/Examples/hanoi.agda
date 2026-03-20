module Examples.hanoi where

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

open import Agda.Builtin.Int
open import CLP.ftUtilsDerivation
open import CLP.types
open import CLP.unifyDisunify
open import CLP.solverScheduler
open import CLP.clp
open import Empty.domain
open import Bool.domain
open import FD.domain
open import Sum.domain

open import ASP.types
open import ASP.asp
open import ASP.dual

open import Examples.myDomainGroup

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  hanoi : FD → FD → Functor
  move : FD → FD → FD → Functor
  move₀ : FD → FD → FD → FD → FD → FD → Functor
  negmove : FD → FD → FD → Functor
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
          aspUtils .fillWithVars (fnot x) n = (fnot ∘ fillWithVars x) n
          aspUtils .fillWithVars (hanoi x y) n = hanoi (varFD n) ((varFD ∘ suc) n)
          aspUtils .fillWithVars (move x y z) n = move (varFD n) ((varFD ∘ suc) n) ((varFD ∘ suc ∘ suc) n)
          aspUtils .fillWithVars (move₀ x y z a b c) n = 
            move₀ 
            (varFD n) 
            ((varFD ∘ suc) n) 
            ((varFD ∘ suc ∘ suc) n) 
            ((varFD ∘ suc ∘ suc ∘ suc) n) 
            ((varFD ∘ suc ∘ suc ∘ suc ∘ suc) n) 
            ((varFD ∘ suc ∘ suc ∘ suc ∘ suc ∘ suc) n)
          aspUtils .fillWithVars (negmove x y z) n = negmove (varFD n) ((varFD ∘ suc) n) ((varFD ∘ suc ∘ suc) n)
          aspUtils .fillWithVars ffalse n = ffalse

-- These are general functions that we need in the generic CLP scheme.
instance  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch (fnot x) (fnot y) = zipMatch atomUtils x y
          atomUtils .zipMatch (hanoi a b) (hanoi x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (move a b c) (move x y z) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ (_:-:_ FD𝒞 (c =ℒ z)) ∷ [])
          atomUtils .zipMatch (move₀ a b c d e f) (move₀ x y z g h i) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ 
                  (_:-:_ FD𝒞 (d =ℒ g)) ∷ (_:-:_ FD𝒞 (e =ℒ h)) ∷ (_:-:_ FD𝒞 (f =ℒ i)) ∷ [])
          atomUtils .zipMatch (negmove a b c) (negmove x y z) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ (_:-:_ FD𝒞 (c =ℒ z)) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a b → hanoi (incrementFD n a) (incrementFD n b))
              (λ a b c → move (incrementFD n a) (incrementFD n b) (incrementFD n c))
              (λ a b c d e f → move₀ 
                (incrementFD n a) 
                (incrementFD n b) 
                (incrementFD n c) 
                (incrementFD n d) 
                (incrementFD n e) 
                (incrementFD n f))
              (λ a b c → negmove (incrementFD n a) (incrementFD n b) (incrementFD n c))
              ffalse

-- the streamreasoning example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  hanoiProgram :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  hanoiProgram = do
    N ← new
    T ← new

    hanoi N T :-
      move₀ N (＃ (pos 0)) T (＃ (pos 0)) (＃ (pos 1)) (＃ (pos 2)) •ₐ
    
    N ← new
    Ti ← new
    Tf ← new
    T1 ← new
    T2 ← new
    Pi ← new
    Pf ← new
    Px ← new
    N1 ← new

    move₀ N Ti Tf Pi Pf Px :-
      FD𝒞 ↪ N ＃> ＃ (pos 1) ∧
      FD𝒞 ↣ N1 =ℒ N ＃- ＃ (pos 1) ∧
      move₀ N1 Ti T1 Pi Px Pf ∧ₐ
      move₀ (＃ (pos 1)) T1 T2 Pi Pf Px ∧ₐ
      move₀ N1 T2 Tf Px Pf Pi •ₐ
    
    move₀ (＃ (pos 1)) Ti Tf Pi Pf Px :-
      FD𝒞 ↪ N ＃> ＃ (pos 1) ∧
      FD𝒞 ↣ Tf =ℒ Ti ＃+ ＃ (pos 1) ∧
      move Pi Pf Tf •ₐ

    move Pi Pf T :- not (negmove Pi Pf T) •ₐ
    negmove Pi Pf T :- not (move Pi Pf T) •ₐ

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    hanoi (＃ (pos 3)) (＃ (pos 3)) •ₐ

  execute = (head ∘ aspExecute hanoiProgram) question

  getDuals = computeDuals (toIntern hanoiProgram)