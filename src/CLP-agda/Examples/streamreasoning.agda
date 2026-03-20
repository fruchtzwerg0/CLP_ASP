module Examples.streamreasoning where

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

open import ASP.types
open import ASP.asp
open import ASP.dual

open import Examples.myDomainGroup

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  validStream : FD → ⊎Logic BoolLogic BoolLogic → Functor
  stream : FD → ⊎Logic BoolLogic BoolLogic → Functor
  cancelled : FD → ⊎Logic BoolLogic BoolLogic → Functor
  higherPrio : FD → FD → Functor
  incompt : ⊎Logic BoolLogic BoolLogic → ⊎Logic BoolLogic BoolLogic → Functor
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
          aspUtils .fillWithVars (validStream x y) n = validStream (varFD n) ((var⊎ ∘ suc) n)
          aspUtils .fillWithVars (stream x y) n = stream (varFD n) ((var⊎ ∘ suc) n)
          aspUtils .fillWithVars (cancelled x y) n = cancelled (varFD n) ((var⊎ ∘ suc) n)
          aspUtils .fillWithVars (higherPrio x y) n = higherPrio (varFD n) ((varFD ∘ suc) n)
          aspUtils .fillWithVars (incompt x y) n = incompt (var⊎ n) ((var⊎ ∘ suc) n)
          aspUtils .fillWithVars ffalse n = ffalse

-- These are general functions that we need in the generic CLP scheme.
instance  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch (fnot x) (fnot y) = zipMatch atomUtils x y
          atomUtils .zipMatch (validStream a b) (validStream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch (stream a b) (stream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch (cancelled a b) (cancelled x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch (higherPrio a b) (higherPrio x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (incompt a b) (incompt x y) = 
            just ((_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (a =ℒ x) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a b → validStream (incrementFD n a) (increment⊎ n b))
              (λ a b → stream (incrementFD n a) (increment⊎ n b))
              (λ a b → cancelled (incrementFD n a) (increment⊎ n b))
              (λ a b → higherPrio (incrementFD n a) (incrementFD n b))
              (λ a b → incompt (increment⊎ n a) (increment⊎ n b))
              ffalse

-- the streamreasoning example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  streamReasoning :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  streamReasoning = do
    P ← new
    Data ← new

    validStream P Data :-
      stream P Data ∧ₐ
      not (cancelled P Data) •ₐ
    
    P1 ← new
    Data1 ← new

    cancelled P Data :-
      higherPrio P1 P ∧ₐ
      stream P1 Data1 ∧ₐ
      incompt Data Data1 •ₐ
    
    PHi ← new
    PLo ← new

    higherPrio PHi PLo :-
      FD𝒞 ↪ PHi ＃> PLo •

    X ← new

    incompt (p X) (q X) •
    incompt (q X) (p X) •

    stream (＃ (pos 0)) (p X) •
    stream (＃ (pos 1)) (q true) •
    stream (＃ (pos 2)) (q false) •
    stream (＃ (pos 3)) (p true) •

  question :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    validStream (varFD 0) (var⊎ 1) •ₐ

  execute = (head ∘ aspExecute streamReasoning) question

  getDuals = computeDuals (toIntern streamReasoning)