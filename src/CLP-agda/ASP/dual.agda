{-# OPTIONS --allow-unsolved-metas #-}

module ASP.dual where

open import Term.types
open import Term.ftUtilsDerivation
open import Term.utilities
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

toASPAtom : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → Atom
  → ASPAtom Atom 𝒞 Code Constraint
toASPAtom x = wrap x 0 []

toASPLiteral : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → Literal Atom 𝒞 Code Constraint 
  → Literal (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
toASPLiteral ⦃ a ⦄ ⦃ cn ⦄ (atom at) = atom ⦃ a ⦄ ⦃ cn ⦄ (toASPAtom at)
toASPLiteral (constraint c) = constraint c

makeTopLevelBody : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → Atom
  → ℕ 
  → List (ASPAtom Atom 𝒞 Code Constraint)
makeTopLevelBody at zero = []
makeTopLevelBody at (suc x) = wrap (ASP.types.not at) (suc x) [] ∷ makeTopLevelBody at x

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

collectVarsWithType : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → Literal Atom 𝒞 Code Constraint
  → List (Σᵢ 𝒞 Code Code Constraint)
collectVarsWithType (constraint (inj₁ (_:-:_ c (x =ℒ y) ⦃ _ ⦄ ⦃ val ⦄ ⦃ _ ⦄ ⦃ _ ⦄))) = 
  zipMatchRecursive ((_:-:_ c x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ (_:-:_ c y ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
collectVarsWithType (constraint (inj₁ (_:-:_ c (x ≠ℒ y) ⦃ _ ⦄ ⦃ val ⦄ ⦃ _ ⦄ ⦃ _ ⦄))) = 
  zipMatchRecursive ((_:-:_ c x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ (_:-:_ c y ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) ∷ [])
collectVarsWithType (constraint (inj₂ (_:-:_ c (default l) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ cn ⦄))) with zipMatch cn c l l 
... | just x = (zipMatchRecursive ∘ Data.List.map (λ { (_:-:_ c₁ (x =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) 
                                                     ; (_:-:_ c₁ (x ≠ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) })) x
... | nothing = []
collectVarsWithType (constraint (inj₂ (_:-:_ c (dual l) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ cn ⦄))) with zipMatch cn c l l 
... | just x = (zipMatchRecursive ∘ Data.List.map (λ { (_:-:_ c₁ (x =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) 
                                                     ; (_:-:_ c₁ (x ≠ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) })) x
... | nothing = []
collectVarsWithType (atom ⦃ _ ⦄ ⦃ cn ⦄ at) with zipMatch cn at at
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
    ((concat ∘ Data.List.map collectVarsWithType) bod)
    ((collectVarsWithType ∘ atom ⦃ ft ⦄ ⦃ at ⦄) hea)

negateLiteral : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → Literal Atom 𝒞 Code Constraint
  → Literal Atom 𝒞 Code Constraint
negateLiteral (atom at) = (atom ∘ toggle) at
negateLiteral (constraint (inj₁ (c₁ :-: (l =ℒ r)))) = constraint (inj₁ (c₁ :-: (l ≠ℒ r)))
negateLiteral (constraint (inj₁ (c₁ :-: (l ≠ℒ r)))) = constraint (inj₁ (c₁ :-: (l =ℒ r)))
negateLiteral (constraint (inj₂ (c₁ :-: (dual l)))) = constraint (inj₂ (c₁ :-: (default l)))
negateLiteral (constraint (inj₂ (c₁ :-: (default l)))) = constraint (inj₂ (c₁ :-: (dual l)))

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
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ DecEq 𝒞 ⦄
  → ℕ
  → ClauseI Atom 𝒞 Code Constraint
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
applyDeMorgan n (hea :-- bod) = let forAllVars = existentialVars (hea :-- bod)
  in unfoldr (λ { (suc x) → just ((wrap (ASP.types.not hea) n forAllVars :-- (Data.List.map toASPLiteral ∘ buildNegatedBody ( ∣ length bod - x ∣ )) bod) , x) ;
                  zero → nothing }) (length bod)

buildForAll : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ℕ
  → List (Σᵢ 𝒞 Code Code Constraint)
  → List (Σᵢ 𝒞 Code Code Constraint)
  → Atom
  → ASPAtom Atom 𝒞 Code Constraint
buildForAll n (v ∷ vars) acc name = forAll v (buildForAll n vars (v ∷ acc) name)
buildForAll n [] acc name = wrap (ASP.types.not name) n acc

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
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ DecEq 𝒞 ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
computeDual ((hea :-- bod) ∷ xs) = 
  ((toASPAtom ∘ ASP.types.not) hea :-- (Data.List.map atom (reverse (makeTopLevelBody hea ((suc ∘ length) xs))))) ∷
  (concat ∘ Data.List.map
    (λ {(n , (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)) → 
      if (_≡ᵇ_ 0 ∘ length ∘ existentialVars) (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)
           then applyDeMorgan (suc n) (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)
           else (wrap (ASP.types.not hea) (suc n) [] :--
              ((atom ∘ buildForAll (suc n) (existentialVars (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄)) []) hea ∷ [])
              ∷ applyDeMorgan (suc n) (_:--_ hea bod ⦃ i0 ⦄ ⦃ i1 ⦄))} ))
           (zipWith _,_ ((upTo ∘ suc ∘ length) xs) ((hea :-- bod) ∷ xs))
computeDual [] = []

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
computeDuals ⦃ _ ⦄ ⦃ at ⦄ x = (concat ∘ Data.List.map computeDual ∘ (groupByKey ClauseI.head (λ x → is-just ∘ zipMatch at x))) x