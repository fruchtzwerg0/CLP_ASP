module Views.find where

open import Data.List 
  using (List; []; _∷_; _++_)
open import Data.Bool
open import Function 
  using (_∘_)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)

-- Whole view copied from Ulf Norell's Dependently Typed Programming in Agda

infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[] : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

data False : Set where
record True : Set where

isTrue : Bool → Set
isTrue true = True
isTrue false = False

isFalse : Bool → Set
isFalse b = isTrue (not b)

satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = isTrue (p x)

data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → satisfies p y → (ys : List A) →
    Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs →
    Find p xs

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x ≡ true → isTrue x
trueIsTrue refl = _

falseIsFalse : {x : Bool} → x ≡ false → isFalse x
falseIsFalse refl = _

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ ._) | it false _ | found xs y py ys =
  found (x ∷ xs) y py ys
find p (x ∷ xs) | it false prf | not-found npxs =
  not-found (falseIsFalse prf :all: npxs)
