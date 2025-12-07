module Term.unifyDisunify where

open import Agda.Builtin.String

open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product
open import Function.Base

open import Term.types
open import Term.ftUtilsDerivation

Subst : Set → Set
Subst A = List (ℕ × A)

ncCheckProhibitedRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))

unifyDisunify : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℕ × (List A)) → List (Subst A)
unifyDisunify (x ∷ xs) ncvar = ?

insert : ∀ {A} → ⦃ FTUtils A ⦄ → ℕ → A → List (ℕ × (List A)) → List (ℕ × (List A))
insert x y l = if any (λ { (l , _) → l ≡ᵇ x }) l
               then Data.List.map (λ { (l , r) → l , y ∷ r }) l
               else (x , (y ∷ [])) ∷ l

first : ∀ {A} → (A → Bool) → List A → Maybe A
first p []       = nothing
first p (x ∷ xs) = if p x then just x else first p xs

-- elem? takes an equality predicate (A → A → Bool)
elem? : ∀ {A} → (A → A → Bool) → A → List A → Bool
elem? _ x []       = false
elem? f x (y ∷ ys) = if f x y then true else elem? f x ys

-- union with custom equality
union : ∀ {A} → (A → A → Bool) → List A → List A → List A
union _ []       ys = ys
union f (x ∷ xs) ys =
  if elem? f x ys
  then union f xs ys
  else x ∷ union f xs ys

-- maybe is for checking if the rule has been applied, outer list is for nondeterminism (and if empty failure), inner list is the new equation list.

aRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
aRule [] _ _ = nothing
aRule (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | just n = just ((right =ℒ left ∷ xs ++ ys , vars) ∷ [])
... | _ | _ = aRule xs (left =ℒ right ∷ ys) vars
aRule (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | just n = just ((right ≠ℒ left ∷ xs ++ ys , vars) ∷ [])
... | _ | _ = aRule xs (left ≠ℒ right ∷ ys) vars

ncDisAddProhibitedRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
ncDisAddProhibitedRule [] _ _ = nothing
ncDisAddProhibitedRule (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | nothing = 
  if any (λ { (l , _) → l ≡ᵇ n }) vars
  then just ((right ≠ℒ left ∷ xs ++ ys , insert n right vars) ∷ [])
  else ncDisAddProhibitedRule xs (left ≠ℒ right ∷ ys) vars
... | _ | _ = ncDisAddProhibitedRule xs (left ≠ℒ right ∷ ys) vars

ncDisCompoundNonDetRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
ncDisCompoundNonDetRule [] _ _ = nothing
ncDisCompoundNonDetRule (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | nothing = 
  if not ((primStringEquality (functor left) (functor right)) ∧ ((length ∘ breakArgs) left ≡ᵇ (length ∘ breakArgs) right))
        then just ((right ≠ℒ left ∷ xs ++ ys , vars) ∷ [])
        else just (Data.List.map (λ { x → (x ∷ xs ++ ys) , vars }) (Data.List.zipWith _≠ℒ_ (breakArgs left) (breakArgs right)))
... | _ | _ = ncDisCompoundNonDetRule xs (left ≠ℒ right ∷ ys) vars

ncCheckProhibitedRule [] _ _ = nothing
ncCheckProhibitedRule (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | nothing with first (_≡ᵇ_ n ∘ proj₁) vars
ncCheckProhibitedRule (left =ℒ right ∷ xs) ys vars | just n | nothing | nothing = ncCheckProhibitedRule xs (left =ℒ right ∷ ys) vars
ncCheckProhibitedRule (left =ℒ right ∷ xs) ys vars | just n | nothing | just m =
  if any (λ x → is-just (unifyDisunify (x =ℒ right ∷ []) [])) (proj₂ m)
  then just ((right ≠ℒ left ∷ xs ++ ys , vars) ∷ []) 
  else (ncCheckProhibitedRule xs (left =ℒ right ∷ ys) vars)
ncCheckProhibitedRule (left =ℒ right ∷ xs) ys vars | _ | _ = ncCheckProhibitedRule xs (left =ℒ right ∷ ys) vars

bRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
bRule [] _ _ = nothing
bRule (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if n ≡ᵇ m 
  then just ((xs ++ ys , vars) ∷ []) 
  else (bRule xs (left =ℒ right ∷ ys) vars)
... | _ | _ = bRule xs (left =ℒ right ∷ ys) vars

cRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
cRule [] _ _ = nothing
cRule (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | nothing = 
  if (primStringEquality (functor left) (functor right)) ∧ ((length ∘ breakArgs) left ≡ᵇ (length ∘ breakArgs) right)
  then just (((Data.List.zipWith _≠ℒ_ (breakArgs left) (breakArgs right) ++ (xs ++ ys)) , vars) ∷ [])
  else just []
... | _ | _ = cRule xs (left =ℒ right ∷ ys) vars

ncUnionizeRule : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
ncUnionizeRule [] _ _ = nothing
ncUnionizeRule (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if true --vars ≡ᵇ unionize vars
  then (ncUnionizeRule xs (left =ℒ right ∷ ys) vars)
  else just (((right =ℒ left ∷ xs ++ ys) , unionize vars) ∷ [])
  where
    unionize = Data.List.map (λ { (name , prohibited) → 
                  if ((name ≡ᵇ n) ∨ (name ≡ᵇ m)) 
                  then name , (union _≡ᵇ_ ∘ Data.List.map prohibited ∘ filter (λ {y → (y ≡ᵇ n) ∨ (y ≡ᵇ m)})) vars
                  else name , prohibited})
... | _ | _ = ncUnionizeRule xs (left =ℒ right ∷ ys)

dRuleWithNCVar : ∀ {A} → ⦃ FTUtils A ⦄ → List (ℒ A) → List (ℒ A) → List (ℕ × (List A)) → Maybe (List (List (ℒ A) × List (ℕ × (List A))))
dRuleWithNCVar [] _ = nothing
dRuleWithNCVar (left =ℒ right ∷ xs) ys vars with varName left
... | just n = 
  if occurs n (xs ++ ys) ∧ not (left ≡ᵇ right)
  then (if occurs left right 
        then just [] 
        else apply left right (xs ++ ys))
  else (dRuleWithNCVar xs (left =ℒ right ∷ ys))
... | _ = dRuleWithNCVar xs (left =ℒ right ∷ ys)