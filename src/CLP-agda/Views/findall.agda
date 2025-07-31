module Views.findall where

open import Views.find
open import Data.List 
  using (List; []; _∷_; _++_)
open import Data.Bool
open import Function 
  using (_∘_)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)

-- slightly different than find, returns a list of all found

infixr 5 _∷₀_
infixr 5 _∷₁_
data SplitList {A : Set} : List A → Set where
  [] : SplitList []
  _∷₀_ : ∀ x {xs} → SplitList xs → SplitList (x ∷ xs)
  _∷₁_ : ∀ x {xs} → SplitList xs → SplitList (x ∷ xs)

first : {A : Set}{xs : List A} → SplitList xs → List A
first [] = []
first (x ∷₀ xs) = x ∷ (first xs)
first (x ∷₁ xs) = first xs

second : {A : Set}{xs : List A} → SplitList xs → List A
second [] = []
second (x ∷₀ xs) = second xs
second (x ∷₁ xs) = x ∷ (second xs)

makeSecond : {A : Set}(xs : List A) → SplitList xs
makeSecond [] = []
makeSecond (x ∷ xs) = x ∷₁ makeSecond xs

forget : {A : Set}{xs : List A} -> SplitList xs -> List A
forget [] = []
forget (x ∷₀ xs) = x ∷ (forget xs)
forget (x ∷₁ xs) = x ∷ (forget xs)

data FindAll {A : Set}(p : A → Bool) : List A → Set where
  matches : {l : List A} → (xs : SplitList l) → All (satisfies p) (first xs) → All (satisfies (not ∘ p)) (second xs) → FindAll p (forget xs)

findAll : ∀ {A} (p : A → Bool) (xs : List A) → FindAll p xs
findAll p [] = matches [] all[] all[]

findAll p (x ∷ xs) with inspect (p x) | findAll p xs
... | it true prf | matches sl allYes allNo =
  matches (x ∷₀ sl)
          (trueIsTrue prf :all: allYes)
          allNo

... | it false prf | matches sl allYes allNo =
  matches (x ∷₁ sl)
          allYes
          (falseIsFalse prf :all: allNo)
