{-# OPTIONS --allow-unsolved-metas #-}

module ASP.dual where

open import CLP.types
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Views.find
open import Views.findall
open import Data.Bool hiding (_≟_)
open import Data.String 
  using (String; _==_)
open import Data.Nat hiding (equal; _≟_)
open import Data.List
open import Data.List.Base
open import Data.List.Membership.DecSetoid using (_∈?_)
open import Data.Maybe 
  using (Maybe; just; nothing; map; is-just)
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Function.Base

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

count : ℕ → List ℕ
count (suc x) = x ∷ count x
count zero = []

{-# TERMINATING #-}
unfoldr : {A B : Set} → (B → Maybe (A × B)) → B → List A
unfoldr f seed with f seed
... | nothing        = []
... | just (x , seed') = x ∷ unfoldr f seed'

decToBool : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

maybeToList : {A : Set} → Maybe (List A) → List A
maybeToList nothing  = []
maybeToList (just x) = x

equal : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄ 
  → Σᵢ 𝒞 Code Code Constraint → Σᵢ 𝒞 Code Code Constraint → Bool
equal (_:-:_ c₀ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ inst ⦄) (_:-:_ c₁ y) with c₀ ≟ c₁
... | yes refl = decToBool (_≟_ ⦃ inst ⦄ x y)
... | no _ = false

without : {A : Set} → (A → A → Bool) → List A → List A → List A
without pred xs ys = filterᵇ (λ x → Data.Bool.not (any (pred x) ys)) xs

toNewLiteral : 
  {Atom : Set}
  {Atom₀ : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ FTUtils Atom₀ ⦄
  → ⦃ AtomUtils Atom₀ 𝒞 Code Constraint ⦄
  → (Atom → Atom₀)
  → Literal Atom 𝒞 Code Constraint 
  → Literal Atom₀ 𝒞 Code Constraint
toNewLiteral ⦃ a ⦄ ⦃ cn ⦄ toNewAtom (atom at) = atom ⦃ a ⦄ ⦃ cn ⦄ (toNewAtom at)
toNewLiteral _ (constraint c) = constraint c

makeTopLevelBody : 
  {Atom : Set}
  {Atom₀ : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → Atom₀)
  → Atom
  → ℕ 
  → List Atom₀
makeTopLevelBody f at zero = []
makeTopLevelBody f at (suc x) = f at (suc x) [] ∷ makeTopLevelBody f at x

zipMatchRecursive : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → List (Σᵢ 𝒞 Code Code Constraint)
  → List (Σᵢ 𝒞 Code Code Constraint)
zipMatchRecursive ((_:-:_ c₁ x ⦃ _ ⦄ ⦃ val ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ xs) with 
  Data.List.map (λ (_:-:_ c x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → 
    (λ { (c₁ :-: (x =ℒ y)) → x ; (c₁ :-: (x ≠ℒ y)) → x }) (zipMatch val c x x)) ((_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ xs)
zipMatchRecursive x | y = Data.List.map (λ {(a , nothing) → a ; (a , just b) → zipMatchRecursive b}) (zipWith _,_ x y)
zipMatchRecursive [] = []

collectLeaves : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → Literal Atom 𝒞 Code Constraint
  → List (Σᵢ 𝒞 Code Code Constraint)
collectLeaves (constraint (inj₁ (_:-:_ c (x =ℒ y) ⦃ _ ⦄ ⦃ val ⦄ ⦃ _ ⦄ ⦃ _ ⦄))) = 
  zipMatchRecursive ((_:-:_ c x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ (_:-:_ c y ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
collectLeaves (constraint (inj₁ (_:-:_ c (x ≠ℒ y) ⦃ _ ⦄ ⦃ val ⦄ ⦃ _ ⦄ ⦃ _ ⦄))) = 
  zipMatchRecursive ((_:-:_ c x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ (_:-:_ c y ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
collectLeaves (constraint (inj₂ (_:-:_ c (default l) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ cn ⦄))) with zipMatch cn c l l 
... | just x = (zipMatchRecursive ∘ Data.List.map (λ { (_:-:_ c₁ (x =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) 
                                                     ; (_:-:_ c₁ (x ≠ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) })) x
... | nothing = []
collectLeaves (constraint (inj₂ (_:-:_ c (dual l) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ cn ⦄))) with zipMatch cn c l l 
... | just x = (zipMatchRecursive ∘ Data.List.map (λ { (_:-:_ c₁ (x =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) 
                                                     ; (_:-:_ c₁ (x ≠ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) })) x
... | nothing = []
collectLeaves (atom ⦃ _ ⦄ ⦃ cn ⦄ at) with zipMatch cn at at
... | just x = (zipMatchRecursive ∘ Data.List.map (λ { (_:-:_ c₁ (x =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) 
                                                     ; (_:-:_ c₁ (x ≠ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) })) x
... | nothing = []

existentialVars : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ DecEq 𝒞 ⦄ 
  → ClauseI Atom 𝒞 Code Constraint 
  → List (Σᵢ 𝒞 Code Code Constraint)
existentialVars (_:--_ hea bod ⦃ ft ⦄ ⦃ at ⦄) = 
  without equal
    ((filterᵇ (λ { (_:-:_ c₁ x ⦃ f ⦄) → (is-just ∘ varName) x }) ∘ concat ∘ Data.List.map collectLeaves) bod)
    ((filterᵇ (λ { (_:-:_ c₁ x ⦃ f ⦄) → (is-just ∘ varName) x }) ∘ collectLeaves ∘ atom ⦃ ft ⦄ ⦃ at ⦄) hea)

negateConstraint : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
  → (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
negateConstraint (inj₁ (c₁ :-: (l =ℒ r))) = inj₁ (c₁ :-: (l ≠ℒ r))
negateConstraint (inj₁ (c₁ :-: (l ≠ℒ r))) = inj₁ (c₁ :-: (l =ℒ r))
negateConstraint (inj₂ (c₁ :-: (dual l))) = inj₂ (c₁ :-: (default l))
negateConstraint (inj₂ (c₁ :-: (default l))) = inj₂ (c₁ :-: (dual l))

negateLiteral : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → Literal Atom 𝒞 Code Constraint
  → Literal Atom 𝒞 Code Constraint
negateLiteral (atom at) = (atom ∘ toggle) at
negateLiteral (constraint x) = (constraint ∘ negateConstraint) x

buildNegatedBody : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ℕ 
  → List (Literal Atom 𝒞 Code Constraint) 
  → List (Literal Atom 𝒞 Code Constraint)
buildNegatedBody (suc n) (x ∷ xs) = x ∷ buildNegatedBody n xs
buildNegatedBody (zero) (x ∷ xs) = negateLiteral x ∷ []
buildNegatedBody _ [] = []

applyDeMorgan : 
  {Atom : Set}
  {Atom₀ : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom₀ 𝒞 Code Constraint ⦄
  → ⦃ FTUtils Atom₀ ⦄
  → ⦃ DecEq 𝒞 ⦄
  → (Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → Atom₀)
  → (Atom → Atom₀)
  → ℕ
  → ClauseI Atom 𝒞 Code Constraint
  → List (ClauseI Atom₀ 𝒞 Code Constraint)
applyDeMorgan f toNewAtom n (hea :-- bod) = let forAllVars = existentialVars (hea :-- bod)
  in unfoldr (λ { (suc x) → just ((f hea n forAllVars :-- ((Data.List.map ∘ toNewLiteral) toNewAtom ∘ buildNegatedBody ( ∣ length bod - x ∣ )) bod) , x) ;
                  zero → nothing }) (length bod)

buildForAll : 
  {Atom : Set}
  {Atom₀ : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → Atom₀)
  → (Σᵢ 𝒞 Code Code Constraint → Atom₀ → Atom₀)
  → ℕ
  → List (Σᵢ 𝒞 Code Code Constraint)
  → List (Σᵢ 𝒞 Code Code Constraint)
  → Atom
  → Atom₀
buildForAll f forA n (v ∷ vars) acc name = forA v (buildForAll f forA n vars (v ∷ acc) name)
buildForAll f forA n [] acc name = f name n acc

normalize : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → ClauseI Atom 𝒞 Code Constraint
  → ClauseI Atom 𝒞 Code Constraint
normalize {_}{C}{Code}{Constraint} (_:--_ hea bod ⦃ ft ⦄ ⦃ at ⦄) = 
  let newHead = (fillWithVars hea ∘ foldr _⊔_ 0 ∘ collectVarsᵥ C Code Constraint) (hea :-- bod) in
    newHead :-- ((Data.List.map (constraint ∘ inj₁) ∘ filterᵇ (λ { (c₁ :-: (x =ℒ y)) → (Data.Bool.not ∘ equal (c₁ :-: x)) (c₁ :-: y) ;
                                                          (c₁ :-: (x ≠ℒ y)) → (Data.Bool.not ∘ equal (c₁ :-: x)) (c₁ :-: y) }) ∘ maybeToList ∘ zipMatch at hea) newHead ++ bod)

computeDual : 
  {Atom : Set}
  {Atom₀ : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom₀ 𝒞 Code Constraint ⦄
  → ⦃ FTUtils Atom₀ ⦄
  → ⦃ DecEq 𝒞 ⦄
  → (Atom → ℕ → List (Σᵢ 𝒞 Code Code Constraint) → Atom₀)
  → (Atom → Atom₀)
  → (Σᵢ 𝒞 Code Code Constraint → Atom₀ → Atom₀)
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI Atom₀ 𝒞 Code Constraint)
computeDual f toNewAtom forA ((hea :-- bod) ∷ xs) = 
  ((toNewAtom ∘ ASP.types.not) hea :-- (Data.List.map atom (reverse (makeTopLevelBody f hea ((suc ∘ length) xs))))) ∷
  (concat ∘ Data.List.map
    (λ {(n , (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)) → 
      if (_≡ᵇ_ 0 ∘ length ∘ existentialVars) (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)
           then applyDeMorgan f toNewAtom (suc n) (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)
           else (f hea (suc n) [] :--
              ((atom ∘ buildForAll f forA (suc n) (existentialVars (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)) []) hea ∷ [])
              ∷ applyDeMorgan f toNewAtom (suc n) (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄))} ))
           (zipWith _,_ ((upTo ∘ suc ∘ length) xs) ((hea :-- bod) ∷ xs))
computeDual _ _ _ [] = []

insertGroup :
  {A B : Set} →
  (key : A → B) →
  (eq  : B → B → Bool) →
  A →
  List (List A) →
  List (List A)
insertGroup key eq x [] =
  (x ∷ []) ∷ []
insertGroup key eq x (g ∷ gs) with head g
... | nothing = g ∷ insertGroup key eq x gs
... | just y with eq (key x) (key y)
...   | true  = (x ∷ g) ∷ gs
...   | false = g ∷ insertGroup key eq x gs

groupByKey :
  ∀ {A B} →
  (key : A → B) →
  (eq  : B → B → Bool) →
  List A →
  List (List A)
groupByKey key eq =
  foldr (insertGroup key eq) []

computeDuals : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ DecEq 𝒞 ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
computeDuals ⦃ _ ⦄ ⦃ at ⦄ =
  concat ∘ (Data.List.map ∘ computeDual (λ at n l → wrap (ASP.types.not at) n l) (λ x → wrap x 0 [])) forAll
  ∘ (groupByKey ClauseI.head (λ x → is-just ∘ zipMatch at x)) ∘ Data.List.map normalize