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
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → List (ℕ × (List (Code c)))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c)))))
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
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (Code c) ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ FTUtils (Constraint c) ⦄ 
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ DecEq (Code c) ⦄
  → ⦃ MakeVar (Code c) ⦄
  → ⦃ Show (Code c) ⦄
  → ⦃ Show (Constraint c) ⦄
  → List ((ℒ ∘ Code) c)
  → List ((ℒ ∘ Code) c)
  → List (ℕ × (List (Code c)))
  → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c))))

aRule : RuleType
ncDisAddProhibitedRule : RuleType
ncDisCompoundNonDetRule : RuleType
ncCheckProhibitedRule : RuleType
bRule : RuleType
cRule : RuleType
ncUnionizeRule : RuleType
dRuleWithNCVar : RuleType

rules : ∀ {𝒞 Code Constraint}
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
    → List ((ℒ ∘ Code) c)
    → List ((ℒ ∘ Code) c)
    → List (ℕ × (List (Code c)))
    → (Maybe ∘ List) (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) × List (ℕ × (List (Code c)))))
rules = (aRule ∷ ncDisAddProhibitedRule ∷ ncDisCompoundNonDetRule ∷ ncCheckProhibitedRule ∷ bRule ∷ cRule ∷ ncUnionizeRule ∷ dRuleWithNCVar ∷ [])

aRule c [] _ _ = nothing
aRule c ⦃ decc ⦄ ⦃ instftval ⦄ ⦃ instval ⦄ ⦃ instftcns ⦄ ⦃ instcns ⦄ ⦃ decval ⦄ (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | just n = just ((Data.List.map (λ l → _:-:_ c l ⦃ instftval ⦄ ⦃ instftcns ⦄ ⦃ decval ⦄) (right =ℒ left ∷ xs ++ ys) , vars) ∷ [])
... | _ | _ = aRule c xs (left =ℒ right ∷ ys) vars
aRule c ⦃ decc ⦄ ⦃ inst ⦄ (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | nothing | just n = just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , vars) ∷ [])
... | _ | _ = aRule c xs (left ≠ℒ right ∷ ys) vars

ncDisAddProhibitedRule c [] _ _ = nothing
ncDisAddProhibitedRule c ⦃ decc ⦄ ⦃ inst ⦄ (left ≠ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | nothing = 
  if any (λ { (l , _) → l ≡ᵇ n }) vars
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , insert n right vars) ∷ [])
  else ncDisAddProhibitedRule c xs (left ≠ℒ right ∷ ys) vars
... | _ | _ = ncDisAddProhibitedRule c xs (left ≠ℒ right ∷ ys) vars
ncDisAddProhibitedRule c (left =ℒ right ∷ xs) ys vars = ncDisAddProhibitedRule c xs (left ≠ℒ right ∷ ys) vars

ncDisCompoundNonDetRule c [] _ _ = nothing
ncDisCompoundNonDetRule c ⦃ decc ⦄ ⦃ inst ⦄ ⦃ val ⦄ ⦃ inst2 ⦄ ⦃ val2 ⦄ ⦃ decval ⦄ (left ≠ℒ right ∷ xs) ys vars with varName left | varName right | zipMatch val c left right
... | nothing | nothing | nothing = just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , vars) ∷ [])
... | nothing | nothing | just y = just (Data.List.map (λ { x → (x ∷ Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄ ⦃ inst2 ⦄ ⦃ decval ⦄) (xs ++ ys)) , vars }) y)
... | _ | _ | _ = ncDisCompoundNonDetRule c xs (left ≠ℒ right ∷ ys) vars
ncDisCompoundNonDetRule c (left =ℒ right ∷ xs) ys vars = ncDisCompoundNonDetRule c xs (left ≠ℒ right ∷ ys) vars

ncCheckProhibitedRule c [] _ _ = nothing
ncCheckProhibitedRule c (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | nothing with first (_≡ᵇ_ n ∘ proj₁) vars
ncCheckProhibitedRule c (left =ℒ right ∷ xs) ys vars | just n | nothing | nothing = ncCheckProhibitedRule c xs (left =ℒ right ∷ ys) vars
ncCheckProhibitedRule {C}{Code}{Constraint} c ⦃ decc ⦄ ⦃ inst ⦄ (left =ℒ right ∷ xs) ys vars | just n | nothing | just m =
  if (not ∘ any (λ x → (not ∘ null ∘ unifyDisunify₀ {C}{Code}{Constraint} c rules [] (x =ℒ right ∷ xs ++ ys) vars) []) ∘ proj₂) m
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right ≠ℒ left ∷ xs ++ ys) , vars) ∷ [])
  else (ncCheckProhibitedRule c xs (left =ℒ right ∷ ys) vars)
ncCheckProhibitedRule c (left =ℒ right ∷ xs) ys vars | _ | _ = ncCheckProhibitedRule c xs (left =ℒ right ∷ ys) vars
ncCheckProhibitedRule c (left ≠ℒ right ∷ xs) ys vars = ncCheckProhibitedRule c xs (left ≠ℒ right ∷ ys) vars

bRule c [] _ _ = nothing
bRule c ⦃ decc ⦄ ⦃ inst ⦄ (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if n ≡ᵇ m 
  then just ((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys) , vars) ∷ []) 
  else (bRule c xs (left =ℒ right ∷ ys) vars)
... | _ | _ = bRule c xs (left =ℒ right ∷ ys) vars
bRule c (left ≠ℒ right ∷ xs) ys vars = bRule c xs (left ≠ℒ right ∷ ys) vars

cRule c [] _ _ = nothing
cRule c ⦃ decc ⦄ ⦃ inst ⦄ ⦃ val ⦄ (left =ℒ right ∷ xs) ys vars with varName left | varName right | zipMatch val c left right
... | nothing | nothing | nothing = just []
... | nothing | nothing | just y = just (((y ++ (Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (xs ++ ys))) , vars) ∷ [])
... | _ | _ | _ = cRule c xs (left =ℒ right ∷ ys) vars
cRule c (left ≠ℒ right ∷ xs) ys vars = cRule c xs (left ≠ℒ right ∷ ys) vars

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

ncUnionizeRule c [] _ _ = nothing
ncUnionizeRule {_}{Code} c ⦃ decc ⦄ ⦃ inst ⦄ (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if (all (λ (x , y) → sameVar x y) ∘ Data.List.zip vars ∘ unionize) vars
  then (ncUnionizeRule c xs (left =ℒ right ∷ ys) vars)
  else just (((Data.List.map (λ l → _:-:_ c l ⦃ inst ⦄) (right =ℒ left ∷ xs ++ ys)) , unionize vars) ∷ [])
  where
    unionize : 
      List (ℕ × (List ∘ Code) c) → List (ℕ × (List ∘ Code) c)
    unionize = Data.List.map (λ { (name , prohibited) → 
                  if ((name ≡ᵇ n) ∨ (name ≡ᵇ m)) 
                  then name , (foldr (union (λ x y → decToBool (x ≟ y))) [] ∘ Data.List.map (λ {(_ , y) → y}) ∘ filterᵇ (λ {(y , _) → (y ≡ᵇ n) ∨ (y ≡ᵇ m)})) vars
                  else name , prohibited })
... | _ | _ = ncUnionizeRule c xs (left =ℒ right ∷ ys) vars
ncUnionizeRule c (left ≠ℒ right ∷ xs) ys vars = ncUnionizeRule c xs (left ≠ℒ right ∷ ys) vars

dRuleWithNCVar c [] _ _ = nothing
dRuleWithNCVar {C}{Code}{Constraint} c ⦃ decc ⦄ ⦃ instCode ⦄ ⦃ instCns ⦄ ⦃ instCode1 ⦄ ⦃ instCns1 ⦄ ⦃ decval ⦄ (left =ℒ right ∷ xs) ys vars with varName left | varName right
... | just n | just m = 
  if occursᵥ {listOf genericConstraint} {⊤} C Code Constraint n (Data.List.map (generalize c ⦃ instCode ⦄ ⦃ instCode1 ⦄) (xs ++ ys)) ∧ not (n ≡ᵇ m)
  then (if occurs n right 
        then just [] 
        else just (((Data.List.map (λ l → _:-:_ c l ⦃ instCode ⦄ ⦃ instCode1 ⦄ ⦃ decval ⦄) ∘ Data.List.map (applyConstraint ⦃ instCns ⦄ c n right)) (xs ++ ys) , vars) ∷ []))
  else (dRuleWithNCVar c xs (left =ℒ right ∷ ys) vars)
... | just n | nothing = 
  if occursᵥ {listOf genericConstraint} {⊤} C Code Constraint n (Data.List.map (generalize c ⦃ instCode ⦄ ⦃ instCode1 ⦄) (xs ++ ys))
  then (if occurs n right 
        then just [] 
        else just (((Data.List.map (λ l → _:-:_ c l ⦃ instCode ⦄ ⦃ instCode1 ⦄ ⦃ decval ⦄) ∘ Data.List.map (applyConstraint ⦃ instCns ⦄ c n right)) (xs ++ ys) , vars) ∷ []))
  else (dRuleWithNCVar c xs (left =ℒ right ∷ ys) vars)
... | _ | _ = dRuleWithNCVar c xs (left =ℒ right ∷ ys) vars
dRuleWithNCVar c (left ≠ℒ right ∷ xs) ys vars = dRuleWithNCVar c xs (left ≠ℒ right ∷ ys) vars

{-# TERMINATING #-}
unifyDisunify₀ witness (r ∷ rs) rs0 unifications dis rest with r witness unifications [] dis
unifyDisunify₀ witness (r ∷ rs) rs0 unifications dis rest | nothing = unifyDisunify₀ witness rs (r ∷ rs0) unifications dis rest
unifyDisunify₀ witness (r ∷ rs) rs0 unifications dis rest | just l = 
  (Data.List.map concat ∘ Data.List.map (λ (newUnif , newDis) → 
    unifyDisunify₀ 
      witness 
      (rs0 ++ r ∷ rs) 
      [] 
      ((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing}) ∘ catMaybes ∘ Data.List.map (getPermission witness) ∘ Data.List.map inj₁) newUnif) 
      newDis 
      (((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing}) ∘ catMaybes ∘ Data.List.map (getElse witness) ∘ Data.List.map inj₁) newUnif) ++ rest))) l
unifyDisunify₀ witness [] _ unifications dis rest = (Data.List.map inj₁ rest ++ Data.List.map (inj₁ ∘ (λ l → _:-:_ witness l)) unifications) ∷ []

-- generic unification and disunification usable with any type.
unifyDisunify : 
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
  → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
unifyDisunify witness unifications = 
  unifyDisunify₀ witness rules [] ((catMaybes ∘ Data.List.map (λ {(inj₁ x) → just x ; (inj₂ _) → nothing})) unifications) [] []

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