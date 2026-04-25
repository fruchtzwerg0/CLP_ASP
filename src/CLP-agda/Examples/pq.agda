module Examples.pq where

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
open import CLP.solverScheduler
open import CLP.clp
open import Empty.domain
open import Bool.domain
open import FD.domain
open import Sum.domain
open import String.domain

open import ASP.types
open import ASP.asp
open import ASP.dual
open import ASP.nmr
open import ASP.loops

open import Examples.myDomainGroup

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  fp : FD → Functor
  fq : FD → Functor
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
instance  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch (fnot x) (fnot y) = zipMatch atomUtils x y
          atomUtils .zipMatch (fp a) (fq x) = 
            just ((_:-:_ fd𝒞 (a =ℒ x)) ∷ [])
          atomUtils .zipMatch (fq a) (fq x) = 
            just ((_:-:_ fd𝒞 (a =ℒ x)) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a → fp (incrementFD n a))
              (λ a → fq (incrementFD n a))
              ffalse
          atomUtils .apply c₀ n z = 
            foldFunctor 
              fnot 
              (λ a → fp (apply valueUtils c₀ fd𝒞 n z a))
              (λ a → fq (apply valueUtils c₀ fd𝒞 n z a))
              ffalse

-- the streamreasoning example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  forallTest :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  forallTest = do
    N ← new
    T ← new

    hanoi N T :-
      move₀ N (＃ (pos 0)) T (~ "a") (~ "b") (~ "c") •ₐ
    
    Ti ← new
    Tf ← new
    T1 ← new
    T2 ← new
    Pi ← new
    Pf ← new
    Px ← new

    move₀ N Ti Tf Pi Pf Px :-
      fd𝒞 ↪ N ＃> ＃ (pos 1) ∧
      move₀ (N ＃- ＃ (pos 1)) Ti T1 Pi Px Pf ∧ₐ
      move₀ (＃ (pos 1)) T1 T2 Pi Pf Px ∧ₐ
      move₀ (N ＃- ＃ (pos 1)) T2 Tf Px Pf Pi •ₐ
    
    move₀ (＃ (pos 1)) Ti Tf Pi Pf Px :-
      fd𝒞 ↣ Tf =ℒ Ti ＃+ ＃ (pos 1) ∧
      move Pi Pf Tf •ₐ

    move Pi Pf T :- not (negmove Pi Pf T) •ₐ
    negmove Pi Pf T :- not (move Pi Pf T) •ₐ

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    hanoi (＃ (pos 4)) (varFD 0) •ₐ

  execute = (take 1 ∘ aspExecute hanoiProgram question) (λ { (wrap (move _ _ _) _ _) → true ; _ → false })

  
  {-# COMPILE GHC execute as execute #-}
  
  real = (toIntern  ∘ proj₂ ∘ applyVars hanoiProgram) 0
  getDuals = computeDuals real
  getNmr = computeNMR real