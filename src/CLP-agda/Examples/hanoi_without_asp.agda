module Examples.hanoi_without_asp where

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
open import Data.String hiding (head)

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
open import FD.domain
open import Product.domain
open import List.domain
open import String.domain

open import Bool.domain
open import CLP.utilities
open import CLP.outputFormatter

open import Examples.myDomainGroup

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor (A : Set) : Set where
  append : ListLogic (×Logic A A) → ListLogic (×Logic A A) → ListLogic (×Logic A A) → Functor A
  hanoi  : FD → A → A → A → ListLogic (×Logic A A) → Functor A
  hanoiMoves : FD → ListLogic (×Logic A A) → Functor A

-- custom validation scheme, that can be used to restrict the user from certain constructions that would typecheck.
-- in ASP, we could use it to restrict fnot only to be used in the body, and ffalse only in the head.
-- The top type ⊤ would be used for constructions that are allowed, and the bottom type ⊥ for constructions that are illegal.
validate : ∀ {A} → Where → Functor A → Set
validate _ _ = ⊤

functorD : HasDesc Functor
functorD = deriveDesc Functor

-- we need to derive ftUtils for our atom type
instance  ftUtilsFunctor : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (Functor A)
          ftUtilsFunctor = deriveFTUtils functorD

-- a fold to be used for increment later.
foldFunctor = deriveFold functorD

-- These are general functions that we need in the generic CLP scheme.
instance  atomUtils : (c : My𝒞) → ⦃ FTUtils ⟦ c ⟧ ⦄ → ⦃ FTUtils ⟦ c ⟧ℒ ⦄ → ⦃ DecEq ⟦ c ⟧ ⦄ → ⦃ MakeVar ⟦ c ⟧ ⦄ → ⦃ Show ⟦ c ⟧ ⦄ → ⦃ Show ⟦ c ⟧ℒ ⦄ → AtomUtils (Functor ⟦ c ⟧) My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils co ⦃ ft ⦄ ⦃ ftc ⦄ ⦃ dec ⦄ ⦃ mkv ⦄ ⦃ sho ⦄ ⦃ shoc ⦄ .zipMatch (append a b c) (append x y z) = 
            just ((_:-:_ (list𝒞 (×𝒞 co co)) (a =ℒ x)) ∷ (_:-:_ (list𝒞 (×𝒞 co co)) (b =ℒ y)) ∷ (_:-:_ (list𝒞 (×𝒞 co co)) (c =ℒ z)) ∷ [])
          atomUtils co ⦃ ft ⦄ ⦃ ftc ⦄ ⦃ dec ⦄ ⦃ mkv ⦄ ⦃ sho ⦄ ⦃ shoc ⦄ .zipMatch (hanoi a b c d e) (hanoi x y z f g) = 
            just ((_:-:_ fd𝒞 (a =ℒ x)) ∷ (_:-:_ co (b =ℒ y)) ∷ (_:-:_ co (c =ℒ z)) ∷ (_:-:_ co (d =ℒ f)) ∷ (_:-:_ (list𝒞 (×𝒞 co co)) (e =ℒ g)) ∷ [])
          atomUtils co ⦃ ft ⦄ ⦃ ftc ⦄ ⦃ dec ⦄ ⦃ mkv ⦄ ⦃ sho ⦄ ⦃ shoc ⦄ .zipMatch (hanoiMoves a b) (hanoiMoves x y) = 
            just ((_:-:_ fd𝒞 (a =ℒ x)) ∷ (_:-:_ (list𝒞 (×𝒞 co co)) (b =ℒ y)) ∷ [])
          atomUtils _ .zipMatch _ _ = nothing
          atomUtils co .increment n = 
            foldFunctor 
              (λ a b c → append (increment valueUtils (list𝒞 (×𝒞 co co)) n a) (increment valueUtils (list𝒞 (×𝒞 co co)) n b) (increment valueUtils (list𝒞 (×𝒞 co co)) n c))
              (λ a b c d e → hanoi (incrementFD n a) (increment valueUtils co n b) (increment valueUtils co n c) (increment valueUtils co n d) (increment valueUtils (list𝒞 (×𝒞 co co)) n e))
              (λ a b → hanoiMoves (incrementFD n a) (increment valueUtils (list𝒞 (×𝒞 co co)) n b))

module program where
  open CLP.types

  appendProgram :
    (c : My𝒞) →
    ⦃ FTUtils ⟦ c ⟧ ⦄ →
    ⦃ MakeVar ⟦ c ⟧ ⦄ →
    ⦃ AtomUtils (Functor ⟦ c ⟧) My𝒞 ⟦_⟧ ⟦_⟧ℒ ⦄ →
    Clause (Functor ⟦ c ⟧) validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  appendProgram c = do

    L ← new

    append [] L L •

    H  ← new
    T  ← new
    L2 ← new
    R  ← new

    append (H ∷ T) L2 (H ∷ R) :-
        append T L2 R •ₐ

  hanoiProgram :
    ⦃ AtomUtils (Functor StringLogic) My𝒞 ⟦_⟧ ⟦_⟧ℒ ⦄ →
    Clause (Functor StringLogic) validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  hanoiProgram = do
    appendProgram fd𝒞

    A ← new
    B ← new
    X ← new

    hanoi (＃ (pos 1)) A B X ((A ∶ B) ∷ []) •

    N      ← new
    C     ← new
    Moves  ← new
    Moves1 ← new
    Moves2 ← new

    hanoi N A B C Moves :-
      fd𝒞 ↪ N ＃> ＃ (pos 1) ∧
      hanoi (N ＃- ＃ (pos 1)) A C B Moves1 ∧ₐ
      hanoi (N ＃- ＃ (pos 1)) C B A Moves2 ∧ₐ
      append Moves1 ((A ∶ B) ∷ Moves2) Moves •ₐ

    let a = ~ "a"
    let b = ~ "b"
    let c = ~ "c"

    hanoiMoves N Moves :-
        hanoi N a b c Moves •ₐ

  question :
    ⦃ AtomUtils (Functor StringLogic) My𝒞 ⟦_⟧ ⟦_⟧ℒ ⦄ →
    Body (Functor StringLogic) (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question = 
    hanoiMoves (＃ (pos 3)) (varList 0) •ₐ
  
  execute : (List ∘ List) String
  execute = (take 1 ∘ 
    defaultExecute 
      ⦃ decMy𝒞 ⦄ 
      ⦃ ftUtilsFunctor ⦃ ftUtilsString ⦄ ⦄ 
      ⦃ constraintUtils ⦄
      ⦃ valueUtils ⦄ 
      ⦃ atomUtils string𝒞 ⦄ 
      ⦃ solver ⦄ 
      true
      (hanoiProgram ⦃ atomUtils string𝒞 ⦄)) (question ⦃ atomUtils string𝒞 ⦄)
  
  {-# COMPILE GHC execute as execute #-}