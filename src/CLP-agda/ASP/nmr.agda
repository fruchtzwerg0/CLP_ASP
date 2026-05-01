module ASP.nmr where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
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

{-# TERMINATING #-}
mod : ℕ → ℕ → ℕ
mod n zero = n
mod n m with compare n m
... | less _ _ = n
... | _ = mod (n ∸ m) m

index : {A : Set} → ℕ → List A → Maybe A
index _ [] = nothing
index zero (x ∷ xs) = just x
index (suc n) (x ∷ xs) = index n xs

takeUntilMatch : ∀ {a} {A : Set a} → (A → Bool) → List A → Maybe (List A)
takeUntilMatch p [] = nothing
takeUntilMatch p (x ∷ xs) with p x
... | false = just (x ∷ [])
... | true  = Data.Maybe.map (x ∷_) (takeUntilMatch p xs)

cleanNot :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → Atom
  → Atom
cleanNot a = if isNot a then toggle a else a

equalAtom :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → Atom
  → Atom
  → Bool
equalAtom ⦃ at ⦄ a0 = is-just ∘ zipMatch at (cleanNot a0) ∘ cleanNot

toClause :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → Atom × ℕ
  → Maybe (ClauseI Atom 𝒞 Code Constraint)
toClause program (a , n) = (index n ∘ filterᵇ (equalAtom a ∘ ClauseI.head)) program

getClauses :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → Atom
  → List (ClauseI Atom 𝒞 Code Constraint)
getClauses program a = filterᵇ (equalAtom a ∘ ClauseI.head) program

getAdjacent :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
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
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → (stack : List (Atom × ℕ))
  → (visited : List (Atom × ℕ))
  → (curr : Atom × ℕ)
  → List (Atom × ℕ) × List (Atom × ℕ)
findOLON₀ ⦃ at ⦄ program stack visited curr 
  with takeUntilMatch ((λ x y → (Data.Bool.not ∘ equalAtom ⦃ at ⦄ (proj₁ x) ∘ proj₁) y) curr) stack | 
       any ((λ x y → equalAtom ⦃ at ⦄ (proj₁ x) (proj₁ y)) curr) visited
... | just (y ∷ ys) | _ = 
  if mod ((length ∘ filterᵇ (isNot ∘ proj₁)) (curr ∷ y ∷ ys)) 2 ≡ᵇ 1 
  then curr ∷ y ∷ ys , visited
  else [] , visited
... | just [] | _ = [] , visited
... | nothing | true = [] , visited
... | nothing | false with getAdjacent program curr
... | nothing = [] , visited
... | just x = foldr (λ newCurr (newResults , newVisited) → 
  let result = findOLON₀ program (curr ∷ stack) newVisited newCurr
  in proj₁ result ++ newResults , proj₂ result) ([] , curr ∷ visited) x

findOLON :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI Atom 𝒞 Code Constraint)
findOLON ⦃ at ⦄ program = ((catMaybes ∘ (Data.List.map ∘ toClause) program) ∘ proj₁ ∘ foldr (λ clause (acc , visited) → 
  if any ((equalAtom ∘ proj₁) clause) (Data.List.map proj₁ visited)
  then acc , visited
  else (proj₁ ∘ findOLON₀ program [] visited) clause ++ acc , 
       (proj₂ ∘ findOLON₀ program [] visited) clause) ([] , []) ∘ concat ∘ Data.List.map (λ y → 
    (zipWith _,_ (Data.List.map ClauseI.head y) ∘ upTo ∘ length) y) ∘ groupByKey ClauseI.head (λ y → is-just ∘ zipMatch at y)) program

bodyEq :
  ∀ {Atom 𝒞 Code Constraint}
  → List (Literal Atom 𝒞 Code Constraint)
  → List (Literal Atom 𝒞 Code Constraint)
  → Bool
bodyEq []                              []                              = true
bodyEq []                              (_ ∷ _)                         = false
bodyEq (_ ∷ _)                         []                              = false
bodyEq (atom ⦃ _ ⦄ ⦃ at₁ ⦄ a₁ ∷ b₁)
       (atom ⦃ _ ⦄ ⦃ at₂ ⦄ a₂ ∷ b₂) =
  is-just (zipMatch at₁ a₁ a₂) Data.Bool.∧ bodyEq b₁ b₂
bodyEq (constraint _ ∷ b₁) (constraint _ ∷ b₂) =
  bodyEq b₁ b₂
bodyEq _ _ = false

dedupOLON :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI Atom 𝒞 Code Constraint)
dedupOLON {Atom}{𝒞}{Code}{Constraint} ⦃ at ⦄ ⦃ asp ⦄ = go []
  where
    sameClause :
      ClauseI Atom 𝒞 Code Constraint → ClauseI Atom 𝒞 Code Constraint → Bool
    sameClause c d =
      equalAtom ⦃ at ⦄ ⦃ asp ⦄ (ClauseI.head c) (ClauseI.head d)
      Data.Bool.∧ bodyEq (ClauseI.body c) (ClauseI.body d)

    go : List (ClauseI Atom 𝒞 Code Constraint) → List (ClauseI Atom 𝒞 Code Constraint) → List (ClauseI Atom 𝒞 Code Constraint)
    go acc [] = reverse acc
    go acc (x ∷ xs) =
      if any (sameClause x) acc
        then go acc xs
        else go (x ∷ acc) xs

toChk : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → (ℕ × ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
  → ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
toChk ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄ (n , x) =
  _:--_
    (chk n 0
      ((filterᵇ (λ { (_:-:_ _ v ⦃ _ ⦄) → is-just (varName v) })
         ∘ collectLeaves ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄
         ∘ atom ⦃ ClauseI.inst x ⦄ ⦃ ClauseI.instAt x ⦄) (ClauseI.head x)))
    (ClauseI.body x)
    ⦃ ClauseI.inst x ⦄ ⦃ ClauseI.instAt x ⦄

makeNMRRule : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → (ℕ × ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
makeNMRRule (n , x) with (ASP.types.isFalse ∘ ClauseI.head) x
makeNMRRule ⦃ cns ⦄ ⦃ val ⦄ ⦃ asp ⦄ ⦃ dec ⦄ (n , x) | true  = 
  (computeDual ⦃ cns ⦄ ⦃ val ⦄ ⦃ asp ⦄ ⦃ ClauseI.instAt x ⦄ ⦃ ClauseI.inst x ⦄ 
  (λ { (chk x y l₀) n l₁ → chk x n (l₀ ++ l₁) ; x _ _ → x }) id forAll ∘ [_] ∘ toChk ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄) (n , x)
makeNMRRule ⦃ cns ⦄ ⦃ val ⦄ ⦃ asp ⦄ ⦃ dec ⦄ (n , x) | false = 
  (computeDual ⦃ cns ⦄ ⦃ val ⦄ ⦃ asp ⦄ ⦃ ClauseI.instAt x ⦄ ⦃ ClauseI.inst x ⦄ 
  (λ { (chk x y l₀) n l₁ → chk x n (l₀ ++ l₁) ; x _ _ → x }) id forAll ∘ [_] ∘ toChk ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄) (n , appendNotSelf x)
  where
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
    ... | (just (atom ⦃ ft ⦄ ⦃ at ⦄ y)) with (is-just ∘ zipMatch at (ClauseI.head x) ∘ toggle) y
    ... | true = x
    ... | false = _:--_ (ClauseI.head x) (ClauseI.body x ++ ((atom ⦃ ft ⦄ ⦃ at ⦄ ∘ toggle ∘ ClauseI.head) x) ∷ []) ⦃ ft ⦄ ⦃ at ⦄

makeTopLevelBodyForNMR : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → ℕ × ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
  → ASPAtom Atom 𝒞 Code Constraint
makeTopLevelBodyForNMR (n , x) with (ASP.types.isFalse ∘ ClauseI.head) x
makeTopLevelBodyForNMR ⦃ cns ⦄ ⦃ val ⦄ ⦃ asp ⦄ ⦃ aspa ⦄ ⦃ dec ⦄ (n , x) | true = 
  (ClauseI.head ∘ toChk ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄) (n , x)
makeTopLevelBodyForNMR ⦃ cns ⦄ ⦃ val ⦄ ⦃ asp ⦄ ⦃ aspa ⦄ ⦃ dec ⦄ (n , x) | false = 
  if (_≡ᵇ_ 0 ∘ length ∘ filterᵇ (λ { (_:-:_ c₁ x ⦃ f ⦄) → (is-just ∘ varName) x }) 
  ∘ collectLeaves ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄ ∘ atom ⦃ ClauseI.inst x ⦄ ⦃ ClauseI.instAt x ⦄) (ClauseI.head x)
  then (ClauseI.head ∘ toChk ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄) (n , x)
  else (buildForAll
          -- Preserve the chk's depth y; buildForAll appends the
          -- new forall variable into the chk's arg list.
          (λ { (chk x y l₀) _ l₁ → chk x y (l₀ ++ l₁) ; x _ _ → x })
          forAll n
          ((filterᵇ (λ { (_:-:_ c₁ x ⦃ f ⦄) → (is-just ∘ varName) x }) 
            ∘ collectLeaves ⦃ cns ⦄ ⦃ val ⦄ ⦃ dec ⦄ ∘ atom ⦃ ClauseI.inst x ⦄ ⦃ ClauseI.instAt x ⦄) (ClauseI.head x))
          []
          -- Start from a chk with EMPTY arg list; buildForAll will
          -- populate it as it wraps each forall.  Without this, the
          -- args from toChk would get duplicated by buildForAll's
          -- re-appending.
          (chk n 0 []))

-- computes the NMR rules
computeNMR : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ DecEq 𝒞 ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint)
computeNMR x
  with (Data.List.map normalize ∘ dedupOLON ∘ findOLON) x
       ++ (Data.List.map normalize ∘ filterᵇ (ASP.types.isFalse ∘ ClauseI.head)) x
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
addNMR (atom ⦃ ft ⦄ ⦃ at ⦄ x ∷ xs) = atom (toNewAtom ⦃ at ⦄ x) ∷ addNMR xs
addNMR (constraint x ∷ xs) = constraint x ∷ addNMR xs