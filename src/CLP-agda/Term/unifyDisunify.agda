module Term.unifyDisunify where

open import Agda.Builtin.String

open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function.Base

open import Term.types hiding (_∧_)
open import Term.ftUtilsDerivation
open import Term.utilities

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

insert : {A : Set} → ℕ → A → List (ℕ × (List A)) → List (ℕ × (List A))
insert x y l = if any (λ { (l , _) → l ≡ᵇ x }) l
               then Data.List.map (λ { (l , r) → l , y ∷ r }) l
               else (x , (y ∷ [])) ∷ l

first : {A : Set} → (A → Bool) → List A → Maybe A
first p []       = nothing
first p (x ∷ xs) = if p x then just x else first p xs

-- elem? takes an equality predicate (A → A → Bool)
elem? : {A : Set} → (A → A → Bool) → A → List A → Bool
elem? _ x []       = false
elem? f x (y ∷ ys) = if f x y then true else elem? f x ys

-- union with custom equality
union : ∀ {A} → (A → A → Bool) → List A → List A → List A
union _ []       ys = ys
union f (x ∷ xs) ys =
  if elem? f x ys
  then union f xs ys
  else x ∷ union f xs ys

unifyDisunify₀ : 
  ∀ {𝒞 Code Constraint}
  → (c : 𝒞) 
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄ 
  → ⦃ FTUtils (Constraint c) ⦄ 
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → List ((c : 𝒞)
    → ⦃ FTUtils (Code c) ⦄
    → ⦃ FTUtils (Constraint c) ⦄
    → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → List (ℕ × (List (Code c)))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c)))))
   → List ((c : 𝒞)
    → ⦃ FTUtils (Code c) ⦄
    → ⦃ FTUtils (Constraint c) ⦄
    → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → List (ℕ × (List (Code c)))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c)))))
  → List ((ℒ ∘ Code) c)
  → List (ℕ × (List (Code c)))
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)

-- maybe is for checking if the rule has been applied, outer list is for nondeterminism (and if empty failure), inner list is the new equation list.

RuleType : Set₁
RuleType = ∀ {𝒞 Code Constraint}
  → (c : 𝒞)
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ FTUtils (Constraint c) ⦄
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → List ((ℒ ∘ Code) c)
  → List ((ℒ ∘ Code) c)
  → List (ℕ × (List (Code c)))
  → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c))))

aRule : RuleType
aRule c zipValue [] _ _ = nothing
aRule c ⦃ instCode ⦄ ⦃ instCns ⦄ zipValue (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | just n = just ((Data.List.map (λ l → _:-:_ c l ⦃ instCode ⦄ ⦃ instCns ⦄) (right =ℒ left ∷ xs ++ ys) , vars) ∷ [])
... | _ | _ = aRule c zipValue xs (left =ℒ right ∷ ys) vars
aRule c ⦃ inst ⦄ zipValue (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | just n = just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , vars) ∷ [])
... | _ | _ = aRule c zipValue xs (left ≠ℒ right ∷ ys) vars

ncDisAddProhibitedRule : RuleType
ncDisAddProhibitedRule c zipValue [] _ _ = nothing
ncDisAddProhibitedRule c ⦃ inst ⦄ zipValue (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | nothing = 
  if any (λ { (l , _) → l ≡ᵇ n }) vars
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , insert n right vars) ∷ [])
  else ncDisAddProhibitedRule c zipValue xs (left ≠ℒ right ∷ ys) vars
... | _ | _ = ncDisAddProhibitedRule c zipValue xs (left ≠ℒ right ∷ ys) vars
ncDisAddProhibitedRule c zipValue (left =ℒ right ∷ xs) ys vars = ncDisAddProhibitedRule c zipValue xs (left ≠ℒ right ∷ ys) vars

ncDisCompoundNonDetRule : RuleType
ncDisCompoundNonDetRule c zipValue [] _ _ = nothing
ncDisCompoundNonDetRule c ⦃ inst ⦄ zipValue (left ≠ℒ right ∷ xs) ys vars with varName left | varName right | zipValue c left right
... | nothing | nothing | nothing = just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , vars) ∷ [])
... | nothing | nothing | just y = just (Data.List.map (λ { x → (x ∷ Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys)) , vars }) y)
... | _ | _ | _ = ncDisCompoundNonDetRule c zipValue xs (left ≠ℒ right ∷ ys) vars
ncDisCompoundNonDetRule c zipValue (left =ℒ right ∷ xs) ys vars = ncDisCompoundNonDetRule c zipValue xs (left ≠ℒ right ∷ ys) vars

ncCheckProhibitedRule : RuleType
ncCheckProhibitedRule c zipValue [] _ _ = nothing
ncCheckProhibitedRule c zipValue (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | nothing with first (_≡ᵇ_ n ∘ proj₁) vars
ncCheckProhibitedRule c zipValue (left =ℒ right ∷ xs) ys vars | just n | nothing | nothing = ncCheckProhibitedRule c zipValue xs (left =ℒ right ∷ ys) vars
ncCheckProhibitedRule c ⦃ inst ⦄ zipValue (left =ℒ right ∷ xs) ys vars | just n | nothing | just m =
  if true --any (λ x → is-just (unifyDisunify₀ (x =ℒ right ∷ []) [])) (proj₂ m)
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , vars) ∷ []) 
  else (ncCheckProhibitedRule c zipValue xs (left =ℒ right ∷ ys) vars)
ncCheckProhibitedRule c zipValue (left =ℒ right ∷ xs) ys vars | _ | _ = ncCheckProhibitedRule c zipValue xs (left =ℒ right ∷ ys) vars
ncCheckProhibitedRule c zipValue (left ≠ℒ right ∷ xs) ys vars = ncCheckProhibitedRule c zipValue xs (left ≠ℒ right ∷ ys) vars

bRule : RuleType
bRule c zipValue [] _ _ = nothing
bRule c ⦃ inst ⦄ zipValue (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if n ≡ᵇ m 
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys) , vars) ∷ []) 
  else (bRule c zipValue xs (left =ℒ right ∷ ys) vars)
... | _ | _ = bRule c zipValue xs (left =ℒ right ∷ ys) vars
bRule c zipValue (left ≠ℒ right ∷ xs) ys vars = bRule c zipValue xs (left ≠ℒ right ∷ ys) vars

cRule : RuleType
cRule c zipValue [] _ _ = nothing
cRule c ⦃ inst ⦄ zipValue (left =ℒ right ∷ xs) ys vars with varName left | varName right | zipValue c left right
... | nothing | nothing | nothing = just []
... | nothing | nothing | just y = just (((y ++ (Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys))) , vars) ∷ [])
... | _ | _ | _ = cRule c zipValue xs (left =ℒ right ∷ ys) vars
cRule c zipValue (left ≠ℒ right ∷ xs) ys vars = cRule c zipValue xs (left ≠ℒ right ∷ ys) vars

ncUnionizeRule : RuleType
ncUnionizeRule c zipValue [] _ _ = nothing
ncUnionizeRule c ⦃ inst ⦄ zipValue (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if true --vars ≡ᵇ unionize vars
  then (ncUnionizeRule c zipValue xs (left =ℒ right ∷ ys) vars)
  else just (((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right =ℒ left ∷ xs ++ ys)) , unionize vars) ∷ [])
  where
    unionize : ∀ {A} → List (ℕ × (List A)) → List (ℕ × (List A))
    unionize = Data.List.map (λ { (name , prohibited) → 
                  if ((name ≡ᵇ n) ∨ (name ≡ᵇ m)) 
                  then name , [] --(union _≡ᵇ_ ∘ Data.List.map (λ {(_ , y) → y}) ∘ filter (λ {(y , _) → (y ≡ᵇ n) ∨ (y ≡ᵇ m)})) vars
                  else name , prohibited})
... | _ | _ = ncUnionizeRule c zipValue xs (left =ℒ right ∷ ys) vars
ncUnionizeRule c zipValue (left ≠ℒ right ∷ xs) ys vars = ncUnionizeRule c zipValue xs (left ≠ℒ right ∷ ys) vars

dRuleWithNCVar : RuleType
dRuleWithNCVar c zipValue [] _ _ = nothing
dRuleWithNCVar {C}{Code}{Constraint} c ⦃ instCode ⦄ ⦃ instCns ⦄ zipValue (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if occursᵥ {listOf genericConstraint} {⊤} C Code Constraint n (Data.List.map (generalize c ⦃ instCode ⦄ ⦃ instCns ⦄) (xs ++ ys)) ∧ not (n ≡ᵇ m)
  then (if occurs n right 
        then just [] 
        else nothing) --(just ∘ Data.List.map (apply n right)) (xs ++ ys)) make generic
  else (dRuleWithNCVar c zipValue xs (left =ℒ right ∷ ys) vars)
... | just n | nothing = 
  if occursᵥ {listOf genericConstraint} {⊤} C Code Constraint n (Data.List.map (generalize c ⦃ instCode ⦄ ⦃ instCns ⦄) (xs ++ ys))
  then (if occurs n right 
        then just [] 
        else nothing) --(just ∘ Data.List.map (apply n right)) (xs ++ ys)) make generic
  else (dRuleWithNCVar c zipValue xs (left =ℒ right ∷ ys) vars)
... | _ | _ = dRuleWithNCVar c zipValue xs (left =ℒ right ∷ ys) vars
dRuleWithNCVar c zipValue (left ≠ℒ right ∷ xs) ys vars = dRuleWithNCVar c zipValue xs (left ≠ℒ right ∷ ys) vars

rules : ∀ {𝒞 Code Constraint}
  → List ((c : 𝒞)
    → ⦃ FTUtils (Code c) ⦄
    → ⦃ FTUtils (Constraint c) ⦄
    → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → List (ℕ × (List (Code c)))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c)))))
rules = (aRule ∷ ncDisAddProhibitedRule ∷ ncDisCompoundNonDetRule ∷ ncCheckProhibitedRule ∷ bRule ∷ cRule ∷ ncUnionizeRule ∷ dRuleWithNCVar ∷ [])

{-# TERMINATING #-}
unifyDisunify₀ witness zipValue (r ∷ rs) rs0 unifications dis rest with r witness zipValue unifications unifications dis
unifyDisunify₀ witness zipValue (r ∷ rs) rs0 unifications dis rest | nothing = unifyDisunify₀ witness zipValue rs (r ∷ rs0) unifications dis rest
unifyDisunify₀ witness zipValue (r ∷ rs) rs0 unifications dis rest | just l = 
  (Data.List.map concat ∘ Data.List.map (λ (newUnif , newDis) → 
    unifyDisunify₀ 
      witness 
      zipValue 
      (rs0 ++ r ∷ rs) 
      [] 
      ((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing}) ∘ catMaybes ∘ Data.List.map (getPermission witness) ∘ Data.List.map inj₁) newUnif) 
      newDis 
      (((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing}) ∘ catMaybes ∘ Data.List.map (getElse witness) ∘ Data.List.map inj₁) newUnif) ++ rest))) l
unifyDisunify₀ witness zipValue [] _ unifications dis rest = (Data.List.map inj₁ rest ++ Data.List.map (inj₁ ∘ (λ l → _:-:_ witness l)) unifications) ∷ []

unifyDisunify : 
  ∀ {𝒞 Code Constraint}
  → (c : 𝒞) 
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄ 
  → ⦃ FTUtils (Constraint c) ⦄ 
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
unifyDisunify witness zipValue unifications = 
  unifyDisunify₀ witness zipValue rules [] ((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing})) unifications) [] []