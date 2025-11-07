module Term.types where

open import Data.String
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Nat
open import Data.Fin

open import Generics
open import Generics.Constructions.Fold

data Slot (A : Set) : Set where
  slot : A → Slot A

mutual
  data Nata : Set where
    zero : Nata
    suc  : Slot (Nata ⊎ FT) → Nata

  -- The finite trees datatype (prolog)
  data FT : Set where
    atomT : String → List (Slot (FT ⊎ Nata)) → FT

data DomainDescriptor : Set where
  NataDescriptor : DomainDescriptor
  FTDescriptor : DomainDescriptor
  LogicVarDescriptor : DomainDescriptor

data Domain : DomainDescriptor → Set where
  -- Nata
  zero : Domain NataDescriptor
  suc  : Domain NataDescriptor ⊎ Domain FTDescriptor ⊎ Domain LogicVarDescriptor → Domain NataDescriptor
  -- FT
  atomT : String → List (Domain NataDescriptor ⊎ Domain FTDescriptor ⊎ Domain LogicVarDescriptor) → Domain FTDescriptor
  -- LogicVara
  var : Maybe ℕ → Domain LogicVarDescriptor
  const : {d : DomainDescriptor} → Domain d → Domain LogicVarDescriptor

natD : HasDesc ℕ
natD = deriveDesc ℕ

data Tree’ (A : Set) : Set where
  node : (x : A) (n : ℕ) (xs : Fin n → Tree’ A) → Tree’ A

treeD : HasDesc Tree’
treeD = deriveDesc Tree’

foldTree = deriveFold treeD

sumt2 : Tree’ ℕ → ℕ
sumt2 = foldTree λ x n f → Data.Nat._+_ x (sum (tabulate f))

-- Test data
leaf : Tree’ ℕ
leaf = node 3 0 λ ()

branch : Tree’ ℕ
branch = node 1 2 λ where
  zero    → leaf
  (suc _) → node 2 0 λ ()


data Lists (A : Set) : Set where
  nil  : Lists A
  cons : A → Lists A → Lists A

listD : HasDesc Lists
listD = deriveDesc Lists

--foldList : {A B : Set} → B → (A → B → B) → Lists A → B
foldList = deriveFold listD

sums : Lists ℕ → ℕ
sums = foldList 0 Data.Nat._+_

data Tree (A : Set) : Set where
  node : (x : A) (xs : Lists (Tree A)) → Tree A

treeD2 : HasDesc Tree
treeD2 = deriveDesc Tree

foldTree2 = deriveFold treeD2

sumt : Tree ℕ → ℕ
sumt = foldTree2 λ x xs → Data.Nat._+_ x (foldList Data.Nat._+_ 0 xs)
--foldTree : {A B : Set} → B → (A → B → B) → Tree’ A → B
--foldTree = deriveFold treeD

open Show ⦃...⦄

instance showNat : Show ℕ
         showNat = deriveShow natD

instance showTree : ∀ {A} → ⦃ Show A ⦄ → Show (Tree’ A)
         showTree = deriveShow treeD

domainD : HasDesc Domain
domainD = deriveDesc Domain

--foldDomain : ∀ {d A} → A → (A → A) → Domain d → A
foldDomain = deriveFold domainD
