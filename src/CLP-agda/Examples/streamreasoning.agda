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
open import ASP.nmr

open import Examples.myDomainGroup

open import CLP.utilities

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

-- These are general functions that we need in the generic CLP scheme.
instance  atomUtils : AtomUtils Functor My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils .zipMatch (fnot x) (fnot y) = zipMatch atomUtils x y
          atomUtils .zipMatch (validStream a b) (validStream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ ftUtils⊎ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ dec⊎ ⦄) ∷ [])
          atomUtils .zipMatch (stream a b) (stream x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ ftUtils⊎ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ dec⊎ ⦄) ∷ [])
          atomUtils .zipMatch (cancelled a b) (cancelled x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ ftUtils⊎ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ dec⊎ ⦄) ∷ [])
          atomUtils .zipMatch (higherPrio a b) (higherPrio x y) = 
            just ((_:-:_ FD𝒞 (a =ℒ x)) ∷ (_:-:_ FD𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (incompt a b) (incompt x y) = 
            just ((_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (a =ℒ x) ⦃ ftUtils⊎ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ dec⊎ ⦄) ∷ (_:-:_ (⊎𝒞 Bool𝒞 Bool𝒞) (b =ℒ y) ⦃ ftUtils⊎ ⦄ ⦃ ftUtils⊥ ⦄ ⦃ dec⊎ ⦄) ∷ [])
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

  realStream = (toIntern  ∘ proj₂ ∘ applyVars streamReasoning) 0
  execute = (head ∘ aspExecute streamReasoning) question

  getDuals = computeDuals realStream
  normalizee = ((groupByKey ClauseI.head (λ x → is-just ∘ zipMatch aspAtom x)) ∘ Data.List.map normalize) realStream
  normalizeee = computeDual (λ at n l → wrap (ASP.types.not at) n l) (λ x → wrap x 0 []) forAll ((incompt (var⊎ 7) (var⊎ 8) :--
      (constraint (inj₁ (⊎𝒞 Bool𝒞 Bool𝒞 :-: (p (varBool 6) =ℒ var⊎ 7))) ∷
      constraint (inj₁ (⊎𝒞 Bool𝒞 Bool𝒞 :-: (q (varBool 6) =ℒ var⊎ 8))) ∷
      []))
    ∷
    (incompt (var⊎ 7) (var⊎ 8) :--
      (constraint (inj₁ (⊎𝒞 Bool𝒞 Bool𝒞 :-: (q (varBool 6) =ℒ var⊎ 7))) ∷
      constraint (inj₁ (⊎𝒞 Bool𝒞 Bool𝒞 :-: (p (varBool 6) =ℒ var⊎ 8))) ∷
      []))
    ∷ [])
  exif = existentialVars (validStream (varFD 0) (var⊎ 1) :--
    (atom (stream (varFD 0) (var⊎ 1)) ∷
    atom (fnot (cancelled (varFD 0) (var⊎ 1))) ∷ []))
  zmatch = zipMatchRecursive ((FD𝒞 :-: (＃ pos 0)) ∷ [])
  varTest = varName (varFD 0)
  --hormalize = ASP.dual.equal (FD𝒞 :-: (varFD 0)) (FD𝒞 :-: (＃ (pos 3)))
  collectVaff = collectVarsᵥ My𝒞 ⟦_⟧ ⟦_⟧ℒ realStream

  getNmr = computeNMR realStream