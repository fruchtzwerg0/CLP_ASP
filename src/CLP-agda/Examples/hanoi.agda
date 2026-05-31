{-# OPTIONS --rewriting #-}
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
open import ASP.cforall

open import Examples.myDomainGroup

-- "types" of atoms to be used by the logic program
-- comparable to type declarations in mercury (also hindley-milner)
data Functor : Set where
  fnot    : Functor → Functor
  hanoi : FD → FD → Functor
  move : StringLogic → StringLogic → FD → Functor
  move0 : FD → FD → FD → StringLogic → StringLogic → StringLogic → Functor
  negmove : StringLogic → StringLogic → FD → Functor
  ffalse  : Functor

functorD : HasDesc Functor
functorD = deriveDesc Functor

-- a fold to be used for increment later.
foldFunctor = deriveFold functorD

-- ----------------------------------------------------------------
-- Manual FTUtils for Functor.
--
-- Replaces deriveFTUtils with hand-written instances.  Each
-- method delegates to ftUtilsFD on FD-typed args, ftUtilsString
-- on StringLogic-typed args, and recurses for fnot.  Avoids
-- the massive generic-derivation expansion.
-- ----------------------------------------------------------------
instance ftUtilsFunctor : FTUtils Functor

         ftUtilsFunctor .functor (fnot x)            = functor ⦃ ftUtilsFunctor ⦄ x
         ftUtilsFunctor .functor (hanoi _ _)         = "hanoi"
         ftUtilsFunctor .functor (move _ _ _)        = "move"
         ftUtilsFunctor .functor (move0 _ _ _ _ _ _) = "move0"
         ftUtilsFunctor .functor (negmove _ _ _)     = "negmove"
         ftUtilsFunctor .functor ffalse              = "ffalse"

         ftUtilsFunctor .varName _ = nothing

         ftUtilsFunctor .occurs n (fnot x)            = occurs ⦃ ftUtilsFunctor ⦄ n x
         ftUtilsFunctor .occurs n (hanoi a b)         = occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b
         ftUtilsFunctor .occurs n (move a b c)        = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b ∨ occurs ⦃ ftUtilsFD ⦄ n c
         ftUtilsFunctor .occurs n (move0 a b c d e f) =
           occurs ⦃ ftUtilsFD ⦄ n a ∨ occurs ⦃ ftUtilsFD ⦄ n b ∨ occurs ⦃ ftUtilsFD ⦄ n c ∨
           occurs ⦃ ftUtilsString ⦄ n d ∨ occurs ⦃ ftUtilsString ⦄ n e ∨ occurs ⦃ ftUtilsString ⦄ n f
         ftUtilsFunctor .occurs n (negmove a b c)     = occurs ⦃ ftUtilsString ⦄ n a ∨ occurs ⦃ ftUtilsString ⦄ n b ∨ occurs ⦃ ftUtilsFD ⦄ n c
         ftUtilsFunctor .occurs _ ffalse              = false

         ftUtilsFunctor .collectVars (fnot x)            = collectVars ⦃ ftUtilsFunctor ⦄ x
         ftUtilsFunctor .collectVars (hanoi a b)         =
           collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b
         ftUtilsFunctor .collectVars (move a b c)        =
           collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b Data.List.++ collectVars ⦃ ftUtilsFD ⦄ c
         ftUtilsFunctor .collectVars (move0 a b c d e f) =
           collectVars ⦃ ftUtilsFD ⦄ a Data.List.++ collectVars ⦃ ftUtilsFD ⦄ b Data.List.++ collectVars ⦃ ftUtilsFD ⦄ c Data.List.++
           collectVars ⦃ ftUtilsString ⦄ d Data.List.++ collectVars ⦃ ftUtilsString ⦄ e Data.List.++ collectVars ⦃ ftUtilsString ⦄ f
         ftUtilsFunctor .collectVars (negmove a b c)     =
           collectVars ⦃ ftUtilsString ⦄ a Data.List.++ collectVars ⦃ ftUtilsString ⦄ b Data.List.++ collectVars ⦃ ftUtilsFD ⦄ c
         ftUtilsFunctor .collectVars ffalse              = []

         ftUtilsFunctor .getNat _ = nothing

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
          atomUtils .zipMatch (hanoi a b) (hanoi x y) = 
            just ((_:-:_ fd𝒞 (a =ℒ x)) ∷ (_:-:_ fd𝒞 (b =ℒ y)) ∷ [])
          atomUtils .zipMatch (move a b c) (move x y z) = 
            just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ (_:-:_ fd𝒞 (c =ℒ z)) ∷ [])
          atomUtils .zipMatch (move0 a b c d e f) (move0 x y z g h i) = 
            just ((_:-:_ fd𝒞 (a =ℒ x)) ∷ (_:-:_ fd𝒞 (b =ℒ y)) ∷ (_:-:_ fd𝒞 (c =ℒ y)) ∷ 
                  (_:-:_ string𝒞 (d =ℒ g)) ∷ (_:-:_ string𝒞 (e =ℒ h)) ∷ (_:-:_ string𝒞 (f =ℒ i)) ∷ [])
          atomUtils .zipMatch (negmove a b c) (negmove x y z) = 
            just ((_:-:_ string𝒞 (a =ℒ x)) ∷ (_:-:_ string𝒞 (b =ℒ y)) ∷ (_:-:_ fd𝒞 (c =ℒ z)) ∷ [])
          atomUtils .zipMatch ffalse ffalse = just []
          atomUtils .zipMatch _ _ = nothing
          atomUtils .increment n = 
            foldFunctor 
              fnot 
              (λ a b → hanoi (incrementFD n a) (incrementFD n b))
              (λ a b c → move (incrementString n a) (incrementString n b) (incrementFD n c))
              (λ a b c d e f → move0 
                (incrementFD n a) 
                (incrementFD n b) 
                (incrementFD n c) 
                (incrementString n d) 
                (incrementString n e) 
                (incrementString n f))
              (λ a b c → negmove (incrementString n a) (incrementString n b) (incrementFD n c))
              ffalse
          atomUtils .apply c₀ n z = 
            foldFunctor 
              fnot 
              (λ a b → hanoi (apply valueUtils c₀ fd𝒞 n z a) (apply valueUtils c₀ fd𝒞 n z b))
              (λ a b c → move (apply valueUtils c₀ string𝒞 n z a) (apply valueUtils c₀ string𝒞 n z b) (apply valueUtils c₀ fd𝒞 n z c))
              (λ a b c d e f → move0 
                (apply valueUtils c₀ fd𝒞 n z a) 
                (apply valueUtils c₀ fd𝒞 n z b) 
                (apply valueUtils c₀ fd𝒞 n z c) 
                (apply valueUtils c₀ string𝒞 n z d) 
                (apply valueUtils c₀ string𝒞 n z e) 
                (apply valueUtils c₀ string𝒞 n z f))
              (λ a b c → negmove (apply valueUtils c₀ string𝒞 n z a) (apply valueUtils c₀ string𝒞 n z b) (apply valueUtils c₀ fd𝒞 n z c))
              ffalse

-- the Towers of Hanoi example taken from "Constraint Answer Set Programming without Grounding"
module program where
  open CLP.types

  hanoiProgram :
    Clause Functor validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  hanoiProgram = do
    N ← new
    T ← new

    hanoi N T :-
      move0 N (＃ (pos 0)) T (~ "a") (~ "b") (~ "c") •ₐ
    
    Ti ← new
    Tf ← new
    T1 ← new
    T2 ← new
    Pi ← new
    Pf ← new
    Px ← new

    move0 N Ti Tf Pi Pf Px :-
      fd𝒞 ↪ N ＃> ＃ (pos 1) ∧
      move0 (N ＃- ＃ (pos 1)) Ti T1 Pi Px Pf ∧ₐ
      move0 (＃ (pos 1)) T1 T2 Pi Pf Px ∧ₐ
      move0 (N ＃- ＃ (pos 1)) T2 Tf Px Pf Pi •ₐ
    
    move0 (＃ (pos 1)) Ti Tf Pi Pf Px :-
      fd𝒞 ↣ Tf =ℒ Ti ＃+ ＃ (pos 1) ∧
      move Pi Pf Tf •ₐ

    move Pi Pf T :- not (negmove Pi Pf T) •ₐ
    negmove Pi Pf T :- not (move Pi Pf T) •ₐ

  question1 :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question1 = 
    hanoi (＃ (pos 3)) (varFD 0) •ₐ

  question2 :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question2 = 
    hanoi (＃ (pos 4)) (varFD 0) •ₐ

  question3 :
    Body Functor (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question3 = 
    hanoi (＃ (pos 5)) (varFD 0) •ₐ

  execute1 = (take 1 ∘ aspExecute hanoiProgram question1) (λ { (wrap (move _ _ _) _ _) → true ; _ → false })

  execute2 = (take 1 ∘ aspExecute hanoiProgram question2) (λ { (wrap (move _ _ _) _ _) → true ; _ → false })

  execute3 = (take 1 ∘ aspExecute hanoiProgram question3) (λ { (wrap (move _ _ _) _ _) → true ; _ → false })

  {-# COMPILE GHC execute1 as hExecute1 #-}
  
  {-# COMPILE GHC execute2 as hExecute2 #-}
  
  {-# COMPILE GHC execute3 as hExecute3 #-}