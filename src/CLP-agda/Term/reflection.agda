module Term.reflection where

open import Agda.Builtin.Reflection
open import Reflection hiding (name; Type)
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Data.Char as Char
open import Data.String as String
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.Bool
open import Data.List
open import Agda.Builtin.Sigma

open import Agda.Primitive

collectSlotTypes : Name → Term → TC (List Name)
collectSlotTypes = {!   !}

mMap : ∀ {A B} → (A → TC B) → List A → TC (List B)
mMap f [] = returnTC []
mMap f (x ∷ xs) = do
  res <- f x
  rest <- mMap f xs
  returnTC (res ∷ rest)

deriveDomain : Name → Name → TC ⊤
deriveDomain rootName slotName = do
  domainDescriptor <- freshName "DomainDescriptor"
  declareData domainDescriptor 0 (quoteTerm Set)
  domainNames <- collectSlotTypes domainDescriptor (quoteTerm rootName)
  domainDescriptorConstructors <- (mMap (λ name → do
    descriptorConstructor <- freshName (primStringAppend (showName name) "Descriptor") 
    returnTC (descriptorConstructor , (def domainDescriptor []))) domainNames)
  defineData domainDescriptor domainDescriptorConstructors
  domain <- freshName "Domain"
  declareData domain 0 (quoteTerm Set)
  --defineData domain ()

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
  catchall : ∀ {n} → Fin n