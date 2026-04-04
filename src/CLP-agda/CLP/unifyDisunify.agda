module CLP.unifyDisunify where

open import Agda.Builtin.String

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Function.Base

open import CLP.types hiding (_∧_)
open import CLP.ftUtilsDerivation
open import CLP.utilities

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
  ∀ {A 𝒞 Code Constraint}
  → (c : 𝒞) 
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (occurs : ℕ → A → Bool)
  → (apply : ℕ → Code c → A → A)
  → List ((c : 𝒞)
    → ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils (Code c) ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ FTUtils (Constraint c) ⦄ 
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ DecEq (Code c) ⦄
    → ⦃ MakeVar (Code c) ⦄
    → ⦃ Show (Code c) ⦄
    → ⦃ Show (Constraint c) ⦄
    → (occurs : ℕ → A → Bool)
    → (apply : ℕ → Code c → A → A)
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → A
    → List (ℕ × List (Code c))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × A × List (ℕ × (List (Code c)))))
   → List ((c : 𝒞)
    → ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils (Code c) ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ FTUtils (Constraint c) ⦄ 
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ DecEq (Code c) ⦄
    → ⦃ MakeVar (Code c) ⦄
    → ⦃ Show (Code c) ⦄
    → ⦃ Show (Constraint c) ⦄
    → (occurs : ℕ → A → Bool)
    → (apply : ℕ → Code c → A → A)
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → A
    → List (ℕ × List (Code c))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × A × List (ℕ × (List (Code c)))))
  → List ((ℒ ∘ Code) c)
  → A
  → List (ℕ × List (Code c))
  → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
  → List (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) × A)

-- maybe is for checking if the rule has been applied, outer list is for nondeterminism (and if empty failure), inner list is the new equation list.

RuleType : Set₁
RuleType = ∀ {A 𝒞 Code Constraint}
  → (c : 𝒞)
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (occurs : ℕ → A → Bool)
  → (apply : ℕ → Code c → A → A)
  → List ((ℒ ∘ Code) c)
  → List ((ℒ ∘ Code) c)
  → A
  → List (ℕ × List (Code c))
  → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × A × List (ℕ × List (Code c)))

aRule : RuleType
ncDisAddProhibitedRule : RuleType
ncDisCompoundNonDetRule : RuleType
ncCheckProhibitedRule : RuleType
bRule : RuleType
cRule : RuleType
ncUnionizeRule : RuleType
dRuleWithNCVar : RuleType

rules : ∀ {A 𝒞 Code Constraint}
  → List ((c : 𝒞)
    → ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils (Code c) ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ FTUtils (Constraint c) ⦄ 
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ DecEq (Code c) ⦄
    → ⦃ MakeVar (Code c) ⦄
    → ⦃ Show (Code c) ⦄
    → ⦃ Show (Constraint c) ⦄
    → (occurs : ℕ → A → Bool)
    → (apply : ℕ → Code c → A → A)
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → A
    → List (ℕ × (List (Code c)))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × A × List (ℕ × List (Code c))))
rules = (aRule ∷ ncDisAddProhibitedRule ∷ ncDisCompoundNonDetRule ∷ ncCheckProhibitedRule ∷ bRule ∷ cRule ∷ ncUnionizeRule ∷ dRuleWithNCVar ∷ [])

aRule c oc ap  [] _ other _ = nothing
aRule c ⦃ decc ⦄ ⦃ instftval ⦄ ⦃ instval ⦄ ⦃ instftcns ⦄ ⦃ instcns ⦄ ⦃ decval ⦄ oc ap (left =ℒ right ∷ xs) ys other vars with varName left | varName right
... | nothing | just n = just ((Data.List.map (λ l → _:-:_ c l ⦃ instftval ⦄ ⦃ instftcns ⦄ ⦃ decval ⦄) (right =ℒ left ∷ xs ++ ys) , other , vars) ∷ [])
... | _ | _ = aRule c oc ap xs (left =ℒ right ∷ ys) other vars
aRule c ⦃ decc ⦄ ⦃ inst ⦄ oc ap (left ≠ℒ right ∷ xs) ys other vars with varName left | varName right
... | nothing | just n = just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , other , vars) ∷ [])
... | _ | _ = aRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

ncDisAddProhibitedRule c oc ap [] _ other _ = nothing
ncDisAddProhibitedRule c ⦃ decc ⦄ ⦃ inst ⦄ oc ap (left ≠ℒ right ∷ xs) ys other vars with varName left | varName right
... | just n | nothing = 
  if any (λ { (l , _) → l ≡ᵇ n }) vars
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , other , insert n right vars) ∷ [])
  else ncDisAddProhibitedRule c oc ap xs (left ≠ℒ right ∷ ys) other vars
... | _ | _ = ncDisAddProhibitedRule c oc ap xs (left ≠ℒ right ∷ ys) other vars
ncDisAddProhibitedRule c oc ap (left =ℒ right ∷ xs) ys other vars = ncDisAddProhibitedRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

ncDisCompoundNonDetRule c oc ap [] _ other _ = nothing
ncDisCompoundNonDetRule c ⦃ decc ⦄ ⦃ inst ⦄ ⦃ val ⦄ ⦃ inst2 ⦄ ⦃ val2 ⦄ ⦃ decval ⦄ oc ap (left ≠ℒ right ∷ xs) ys other vars with varName left | varName right | zipMatch val c left right
... | nothing | nothing | nothing = just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , other , vars) ∷ [])
... | nothing | nothing | just y = just (Data.List.map (λ { x → (x ∷ Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄ ⦃ inst2 ⦄ ⦃ decval ⦄) (xs ++ ys)) , other , vars }) y)
... | _ | _ | _ = ncDisCompoundNonDetRule c oc ap xs (left ≠ℒ right ∷ ys) other vars
ncDisCompoundNonDetRule c oc ap (left =ℒ right ∷ xs) ys other vars = ncDisCompoundNonDetRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

ncCheckProhibitedRule c oc ap [] _ other _ = nothing
ncCheckProhibitedRule c oc ap (left =ℒ right ∷ xs) ys other vars with varName left | varName right
... | just n | nothing with first (_≡ᵇ_ n ∘ proj₁) vars
ncCheckProhibitedRule c oc ap (left =ℒ right ∷ xs) ys other vars | just n | nothing | nothing = ncCheckProhibitedRule c oc ap xs (left =ℒ right ∷ ys) other vars
ncCheckProhibitedRule {C}{Code}{Constraint} c ⦃ decc ⦄ ⦃ inst ⦄ oc ap (left =ℒ right ∷ xs) ys other vars | just n | nothing | just m =
  if (not ∘ any (λ x → (not ∘ null ∘ unifyDisunify₀ {C}{Code}{Constraint} c oc ap rules [] (x =ℒ right ∷ xs ++ ys) other vars) []) ∘ proj₂) m
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , other , vars) ∷ [])
  else (ncCheckProhibitedRule c oc ap xs (left =ℒ right ∷ ys) other vars)
ncCheckProhibitedRule c oc ap (left =ℒ right ∷ xs) ys other vars | _ | _ = ncCheckProhibitedRule c oc ap xs (left =ℒ right ∷ ys) other vars
ncCheckProhibitedRule c oc ap (left ≠ℒ right ∷ xs) ys other vars = ncCheckProhibitedRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

bRule c oc ap [] _ other _ = nothing
bRule c ⦃ decc ⦄ ⦃ inst ⦄ oc ap (left =ℒ right ∷ xs) ys other vars with varName left | varName right
... | just n | just m = 
  if n ≡ᵇ m 
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys) , other , vars) ∷ []) 
  else (bRule c oc ap xs (left =ℒ right ∷ ys) other vars)
... | _ | _ = bRule c oc ap xs (left =ℒ right ∷ ys) other vars
bRule c oc ap (left ≠ℒ right ∷ xs) ys other vars = bRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

cRule c oc ap [] _ other _ = nothing
cRule c ⦃ decc ⦄ ⦃ inst ⦄ ⦃ val ⦄ oc ap (left =ℒ right ∷ xs) ys other vars with varName left | varName right | zipMatch val c left right
... | nothing | nothing | nothing = just []
... | nothing | nothing | just y = just (((y ++ (Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys))) , other , vars) ∷ [])
... | _ | _ | _ = cRule c oc ap xs (left =ℒ right ∷ ys) other vars
cRule c oc ap (left ≠ℒ right ∷ xs) ys other vars = cRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

decToBool : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

sameVar : 
  ∀ {A}
  → ⦃ DecEq A ⦄
  → ℕ × (List A)
  → ℕ × (List A)
  → Bool
sameVar (x , y) (a , b) = 
  (x ≡ᵇ a)
  ∧ ((length ∘ union (λ x y → decToBool (x ≟ y)) y) b Data.Nat.≡ᵇ length y)
  ∧ ((length ∘ union (λ x y → decToBool (x ≟ y)) y) b Data.Nat.≡ᵇ length b)

ncUnionizeRule c oc ap [] _ other _ = nothing
ncUnionizeRule {_}{_}{Code} c ⦃ decc ⦄ ⦃ inst ⦄ oc ap (left =ℒ right ∷ xs) ys other vars with varName left | varName right
... | just n | just m = 
  if (all (λ (x , y) → sameVar x y) ∘ Data.List.zip vars ∘ unionize) vars
  then (ncUnionizeRule c oc ap xs (left =ℒ right ∷ ys) other vars)
  else just (((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right =ℒ left ∷ xs ++ ys)) , other , unionize vars) ∷ [])
  where
    unionize : 
      List (ℕ × (List ∘ Code) c) → List (ℕ × (List ∘ Code) c)
    unionize = Data.List.map (λ { (name , prohibited) → 
                  if ((name ≡ᵇ n) ∨ (name ≡ᵇ m)) 
                  then name , (foldr (union (λ x y → decToBool (x ≟ y))) [] ∘ Data.List.map (λ {(_ , y) → y}) ∘ filterᵇ (λ {(y , _) → (y ≡ᵇ n) ∨ (y ≡ᵇ m)})) vars
                  else name , prohibited })
... | _ | _ = ncUnionizeRule c oc ap xs (left =ℒ right ∷ ys) other vars
ncUnionizeRule c oc ap (left ≠ℒ right ∷ xs) ys other vars = ncUnionizeRule c oc ap xs (left ≠ℒ right ∷ ys) other vars

dRuleWithNCVar c oc ap [] _ other _ = nothing
dRuleWithNCVar {_}{C}{Code}{Constraint} c ⦃ decc ⦄ ⦃ instCode ⦄ ⦃ instCns ⦄ ⦃ instCode1 ⦄ ⦃ instCns1 ⦄ ⦃ decval ⦄ oc ap (left =ℒ right ∷ xs) ys other vars with varName left | varName right
... | just n | just m = 
  if (occursᵥ {listOf genericConstraint} {⊤} C Code Constraint n (Data.List.map (generalize c ⦃ instCode ⦄ ⦃ instCode1 ⦄) (xs ++ ys)) ∨ oc n other) ∧ not (n ≡ᵇ m)
  then (if occurs n right 
        then just [] 
        else just (((Data.List.map (λ l → _:-:_ c l ⦃ instCode ⦄ ⦃ instCode1 ⦄ ⦃ decval ⦄) ∘ _∷_ (left =ℒ right) ∘ Data.List.map (applyConstraint ⦃ instCns ⦄ c c n right)) (xs ++ ys) , ap n right other , vars) ∷ []))
  else (dRuleWithNCVar c oc ap xs (left =ℒ right ∷ ys) other vars)
... | just n | nothing = 
  if occursᵥ {listOf genericConstraint} {⊤} C Code Constraint n (Data.List.map (generalize c ⦃ instCode ⦄ ⦃ instCode1 ⦄) (xs ++ ys)) ∨ oc n other
  then (if occurs n right 
        then just [] 
        else just (((Data.List.map (λ l → _:-:_ c l ⦃ instCode ⦄ ⦃ instCode1 ⦄ ⦃ decval ⦄) ∘ _∷_ (left =ℒ right) ∘ Data.List.map (applyConstraint ⦃ instCns ⦄ c c n right)) (xs ++ ys) , ap n right other , vars) ∷ []))
  else (dRuleWithNCVar c oc ap xs (left =ℒ right ∷ ys) other vars)
... | _ | _ = dRuleWithNCVar c oc ap xs (left =ℒ right ∷ ys) other vars
dRuleWithNCVar c oc ap (left ≠ℒ right ∷ xs) ys other vars = dRuleWithNCVar c oc ap xs (left ≠ℒ right ∷ ys) other vars

{-# TERMINATING #-}
unifyDisunify₀ witness oc ap (r ∷ rs) rs0 unifications other dis rest with r witness oc ap unifications [] other dis
unifyDisunify₀ witness oc ap (r ∷ rs) rs0 unifications other dis rest | nothing = unifyDisunify₀ witness oc ap rs (r ∷ rs0) unifications other dis rest
unifyDisunify₀ witness oc ap (r ∷ rs) rs0 unifications other dis rest | just l = 
  (concat ∘ Data.List.map (λ (newUnif , newOther , newDis) → 
    unifyDisunify₀ 
      witness 
      oc
      ap 
      (rs0 ++ r ∷ rs) 
      [] 
      ((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing}) ∘ catMaybes ∘ Data.List.map (getPermission witness) ∘ Data.List.map inj₁) newUnif) 
      newOther
      newDis 
      (((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing}) ∘ catMaybes ∘ Data.List.map (getElse witness) ∘ Data.List.map inj₁) newUnif) ++ rest))) l
unifyDisunify₀ witness oc ap [] _ unifications other dis rest = ((Data.List.map inj₁ rest ++ Data.List.map (inj₁ ∘ (λ l → _:-:_ witness l)) unifications) , other) ∷ []

-- generic unification and disunification usable with any type.
unifyDisunify : 
  ∀ {A 𝒞 Code Constraint}
  → (c : 𝒞) 
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (occurs : ℕ → A → Bool)
  → (apply : ℕ → Code c → A → A)
  → List ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c) × A
  → List (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) × A)
unifyDisunify witness occurs apply (unifications , other) = 
  unifyDisunify₀ witness occurs apply rules [] ((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing})) unifications) other [] []

toVariableView :
  ∀ {𝒞 Code Constraint}
  → (c : 𝒞) 
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → (ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c
  → Maybe ((ℕ × Code c) ⊎ (ℕ × Code c))
toVariableView c (inj₁ (x =ℒ y)) = varName x Data.Maybe.>>= λ z → just (inj₁ (z , y))
toVariableView c (inj₁ (x ≠ℒ y)) = varName x Data.Maybe.>>= λ z → just (inj₂ (z , y))
toVariableView c (inj₂ (default ()))
toVariableView c (inj₂ (dual ()))

toVariableViews :
  ∀ {𝒞 Code Constraint}
  → (c : 𝒞) 
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → List ((ℒ ∘ Code) c ⊎ (Dual ∘ (λ _ → ⊥)) c)
  → List ((ℕ × Code c) ⊎ (ℕ × Code c))
toVariableViews c = catMaybes ∘ Data.List.map (toVariableView c)