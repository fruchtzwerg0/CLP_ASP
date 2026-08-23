module Examples.member where

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
open import List.domain
open import Nat.domain
open import String.domain

open import Bool.domain
open import CLP.utilities
open import CLP.outputFormatter

open import Examples.myDomainGroup

data Functor (A : Set) : Set where
  member : A → ListLogic A → Functor A

validate : ∀ {A} → Where → Functor A → Set
validate _ _ = ⊤

functorD : HasDesc Functor
functorD = deriveDesc Functor

foldFunctor :
  ∀ {A B : Set}
  → (A → ListLogic A → B)
  → Functor A → B
foldFunctor f (member a b) = f a b

instance ftUtilsFunctor : ∀ {A} → ⦃ FTUtils A ⦄ → FTUtils (Functor A)

         ftUtilsFunctor .functor (member _ _) = "member"

         ftUtilsFunctor .varName _ = nothing

         ftUtilsFunctor ⦃ fA ⦄ .occurs n (member a b) =
           occurs ⦃ fA ⦄ n a ∨ occurs ⦃ ftUtilsList ⦃ fA ⦄ ⦄ n b

         ftUtilsFunctor ⦃ fA ⦄ .collectVars (member a b) =
           collectVars ⦃ fA ⦄ a Data.List.++ collectVars ⦃ ftUtilsList ⦃ fA ⦄ ⦄ b

         ftUtilsFunctor .getNat _ = nothing

instance  atomUtils :
            (c : My𝒞)
            → ⦃ FTUtils ⟦ c ⟧ ⦄
            → ⦃ FTUtils ⟦ c ⟧ℒ ⦄
            → ⦃ DecEq ⟦ c ⟧ ⦄
            → ⦃ MakeVar ⟦ c ⟧ ⦄
            → ⦃ Show ⟦ c ⟧ ⦄
            → ⦃ Show ⟦ c ⟧ℒ ⦄
            → AtomUtils (Functor ⟦ c ⟧) My𝒞 ⟦_⟧ ⟦_⟧ℒ
          atomUtils co ⦃ ft ⦄ ⦃ ftc ⦄ ⦃ dec ⦄ ⦃ mkv ⦄ ⦃ sho ⦄ ⦃ shoc ⦄ .zipMatch (member a b) (member x y) =
            just ((_:-:_ co (a =ℒ x)) ∷
                  (_:-:_ (list𝒞 co) (b =ℒ y)) ∷ [])
          atomUtils co .increment n =
            foldFunctor
              (λ a b → member (increment valueUtils co n a)
                              (increment valueUtils (list𝒞 co) n b))
          atomUtils co .apply c₀ n z =
            foldFunctor
              (λ a b → member (apply valueUtils c₀ co n z a)
                              (apply valueUtils c₀ (list𝒞 co) n z b))

module program where
  open CLP.types

  memberProgram :
    ⦃ AtomUtils (Functor NatLogic) My𝒞 ⟦_⟧ ⟦_⟧ℒ ⦄ →
    Clause (Functor NatLogic) validate My𝒞 ⟦_⟧ ⟦_⟧ℒ
  memberProgram = do
    X  ← new
    Xs ← new

    member X (X ∷ Xs) •

    Y    ← new
    T    ← new
    Wild ← new

    member Y (Wild ∷ T) :-
      member Y T •ₐ

  question :
    ⦃ AtomUtils (Functor NatLogic) My𝒞 ⟦_⟧ ⟦_⟧ℒ ⦄ →
    Body (Functor NatLogic) (validate bodyOfRule) My𝒞 ⟦_⟧ ⟦_⟧ℒ
  question =
    member (varNat 0) --(suc (suc zero))
           (suc zero ∷ suc (suc zero) ∷ []) •ₐ

  execute : (List ∘ List) String
  execute = (take 10 ∘
    defaultExecute
      ⦃ decMy𝒞 ⦄
      ⦃ ftUtilsFunctor ⦃ ftUtilsNat ⦄ ⦄
      ⦃ constraintUtils ⦄
      ⦃ valueUtils ⦄
      ⦃ atomUtils nat𝒞 ⦄
      ⦃ solver ⦄
      true
      (memberProgram ⦃ atomUtils nat𝒞 ⦄)) (question ⦃ atomUtils nat𝒞 ⦄)

  {-# COMPILE GHC execute as memberExecute #-}