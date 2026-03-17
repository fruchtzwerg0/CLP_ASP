{-# OPTIONS --allow-unsolved-metas #-}

module ASP.nmr where

open import CLP.types hiding (_>>=_)
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

open import Generics

open import ASP.dual

index : {A : Set} → ℕ → List A → Maybe A
index _ [] = nothing
index zero (x ∷ xs) = just x
index (suc n) (x ∷ xs) = index n xs

takeWhile1 : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
takeWhile1 p []       = []
takeWhile1 p (x ∷ xs) with p x
... | true  = x ∷ takeWhile1 p xs
... | false = []

equalAtom :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → Atom
  → Atom
  → Bool
equalAtom ⦃ at ⦄ a0 = is-just ∘ zipMatch at a0

toClause :
  ∀ {Atom 𝒞 Code Constraint}
  → List (ClauseI Atom 𝒞 Code Constraint)
  → Atom × ℕ
  → Maybe (ClauseI Atom 𝒞 Code Constraint)
toClause program (a , n) = (index n ∘ filterᵇ (equalAtom a ∘ ClauseI.head)) program

getClauses :
  ∀ {Atom 𝒞 Code Constraint}
  → List (ClauseI Atom 𝒞 Code Constraint)
  → Atom
  → List (ClauseI Atom 𝒞 Code Constraint)
getClauses program a = filterᵇ (equalAtom a ∘ ClauseI.head) program

getAdjacent :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → Atom × ℕ
  → (Maybe ∘ List) (Atom × ℕ)
getAdjacent ⦃ at ⦄ program (a , n) = 
  toClause program (a , n) Data.Maybe.>>= just ∘ concat ∘ Data.List.map (λ y → 
    zipWith _,_ (replicate ((length ∘ getClauses program) y) y) ((upTo ∘ length ∘ getClauses program) y)) 
    ∘ catMaybes ∘ Data.List.map (λ { (atom a) → just a ; (constraint _) → nothing }) ∘ ClauseI.body

{-# TERMINATING #-}
findOLON₀ :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → (stack : List (Atom × ℕ))
  → (visited : List (Atom × ℕ))
  → (curr : Atom × ℕ)
  → List (Atom × ℕ) × List (Atom × ℕ)
findOLON₀ ⦃ at ⦄ program stack visited curr 
  with takeWhile1 ((λ x y → equalAtom ⦃ at ⦄ (proj₁ x) (proj₁ y)) curr) stack | 
       any ((λ x y → equalAtom ⦃ at ⦄ (proj₁ x) (proj₁ y)) curr) visited
... | (y ∷ ys) | _ = curr ∷ y ∷ ys , visited
... | [] | true = [] , visited
... | [] | false with getAdjacent program curr
... | nothing = [] , visited
... | just x = foldr (λ newCurr (newResults , newVisited) → 
  (proj₁ ∘ findOLON₀ program (curr ∷ stack) newVisited) newCurr ++ newResults , 
  (proj₂ ∘ findOLON₀ program (curr ∷ stack) newVisited) newCurr) ([] , curr ∷ visited) x

findOLON :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI Atom 𝒞 Code Constraint)
findOLON ⦃ at ⦄ program = ((catMaybes ∘ (Data.List.map ∘ toClause) program) ∘ proj₁ ∘ foldr (λ clause (acc , visited) → 
  if any ((equalAtom ∘ proj₁) clause) (Data.List.map proj₁ visited)
  then acc , visited
  else (proj₁ ∘ findOLON₀ program [] visited) clause ++ acc , 
       (proj₂ ∘ findOLON₀ program [] visited) clause) ([] , []) ∘ concat ∘ Data.List.map (λ y → 
    (zipWith _,_ (Data.List.map ClauseI.head y) ∘ upTo ∘ length) y) ∘ groupByKey ClauseI.head (λ y → is-just ∘ zipMatch at y)) program

appendNotSelf : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ClauseI Atom 𝒞 Code Constraint
  → ClauseI Atom 𝒞 Code Constraint
appendNotSelf x with (ASP.types.isFalse ∘ ClauseI.head) x
... | true = x
... | false with (last ∘ ClauseI.body) x
... | nothing = x
... | (just (constraint _)) = x
... | (just (atom ⦃ _ ⦄ ⦃ at ⦄ y)) with equalAtom ⦃ at ⦄ (ClauseI.head x) y
... | true = x
... | false = _:--_ (ClauseI.head x) (ClauseI.body x ++ (atom ⦃ _ ⦄ ⦃ at ⦄ y) ∷ []) ⦃ _ ⦄ ⦃ at ⦄

toChk : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → (ℕ × ClauseI Atom 𝒞 Code Constraint)
  → ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
toChk ⦃ at ⦄ (n , x) = chk n 0
  ((Data.List.map (λ { (_:-:_ c₁ (x =ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) 
                    ; (_:-:_ c₁ (x ≠ℒ y) ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) → (_:-:_ c₁ x ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) }) 
                    ∘ maybeToList ∘ (zipMatch at ∘ ClauseI.head) x ∘ ClauseI.head) x) :-- 
                    ((Data.List.map ∘ toNewLiteral) (λ x → wrap x 0 []) ∘ ClauseI.body) x

makeNMRRule : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → (ℕ × ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
makeNMRRule (n , x) with (ASP.types.isFalse ∘ ClauseI.head) x
makeNMRRule (n , x) | true  = (computeDual (λ { (chk x y l₀) n l₁ → chk x n (l₀ ++ l₁) ; x _ _ → x }) id forAll ∘ [_] ∘ toChk) (n , x)
makeNMRRule (n , x) | false = (computeDual (λ { (chk x y l₀) n l₁ → chk x n (l₀ ++ l₁) ; x _ _ → x }) id forAll ∘ [_] ∘ toChk) (n , appendNotSelf x)

makeTopLevelBodyForNMR : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ℕ × ClauseI Atom 𝒞 Code Constraint
  → ASPAtom Atom 𝒞 Code Constraint
makeTopLevelBodyForNMR (n , x) with (ASP.types.isFalse ∘ ClauseI.head) x
makeTopLevelBodyForNMR ⦃ ft ⦄ ⦃ at ⦄ (n , x) | true = (ClauseI.head ∘ toChk) (n , x)
makeTopLevelBodyForNMR ⦃ ft ⦄ ⦃ at ⦄ (n , x) | false = 
  if (_≡ᵇ_ 0 ∘ length ∘ collectVarsWithType ∘ atom ⦃ ft ⦄ ⦃ at ⦄ ∘ ClauseI.head) x
  then (ClauseI.head ∘ toChk) (n , x)
  else (buildForAll (λ { (chk x y l₀) n l₁ → chk x n (l₀ ++ l₁) ; x _ _ → x }) forAll n
    ((collectVarsWithType ∘ atom ⦃ ft ⦄ ⦃ at ⦄ ∘ ClauseI.head) x) [] ∘ ClauseI.head ∘ toChk) (n , x)

computeNMR : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
computeNMR x with (Data.List.map normalize ∘ findOLON) x
... | y = (nmrCheck :-- Data.List.map atom ((Data.List.map makeTopLevelBodyForNMR ∘ zipWith _,_ ((upTo ∘ suc ∘ length) y)) y)) ∷ 
  (concat ∘ Data.List.map makeNMRRule ∘ zipWith _,_ ((upTo ∘ suc ∘ length) y)) y

addNMR : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → List (Literal Atom 𝒞 Code Constraint)
  → List (Literal (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
addNMR [] = atom nmrCheck ∷ []
addNMR (atom x ∷ xs) = atom (wrap x 0 []) ∷ addNMR xs
addNMR (constraint x ∷ xs) = constraint x ∷ addNMR xs