module CLP-agda where

open import Data.String 
  using (String; _==_)
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst)
open import Data.List 
  using (List; []; _∷_; _++_; any; all; map; foldl; length; zip; zipWith; concat)
open import Data.Bool
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.Maybe 
  using (Maybe; just; nothing; map)
open import Data.Product 
  using (_,_; Σ)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Data.Unit
open import Data.Product 
  using (_×_; _,_; proj₁; proj₂)
open import Function 
  using (_∘_)

data LogicVar (a : Set) : Set where
  var : Maybe ℕ → LogicVar a
  const : a → LogicVar a

{-# NO_POSITIVITY_CHECK #-}
data Term (f : Set → Set) : Set where
  atomT : String → List (f (Term f)) → Term f

LogicVarTerm : Set
LogicVarTerm = LogicVar (Term LogicVar)

{-# TERMINATING #-}
mapLogicVarTerm : (LogicVarTerm → LogicVarTerm) → LogicVarTerm → LogicVarTerm
mapTerm : (LogicVarTerm → LogicVarTerm) → Term LogicVar → Term LogicVar

mapLogicVarTerm f (var x) = f (var x)
mapLogicVarTerm f (const t) = const (mapTerm f t)

mapTerm f (atomT s args) = atomT s (Data.List.map (mapLogicVarTerm f) args)

data 𝒞 : Set where
  term : 𝒞

⟦_⟧₍𝑑₎ : 𝒞 → (Set → Set) → Set
⟦ term ⟧₍𝑑₎ = Term

mapJust : {A : Set} → (A → A → A) → Maybe A → Maybe A → Maybe A
mapJust f (just n) (just m) = just (f n m)
mapJust _ (just n) nothing = just n
mapJust _ nothing x = x

data Expr : 𝒞 → Set where
  domainExpr : {c : 𝒞} → LogicVar (⟦ c ⟧₍𝑑₎ LogicVar) → Expr c

data ℒ : 𝒞 → Set where
  _=ℒ_ : {c : 𝒞} → Expr c → Expr c → ℒ c

data Atom (c : 𝒞) : Set where
  mkAtom : String
       → List (Expr c)
       → Atom c

data Literal (c : 𝒞) : Set where
  atomLiteral : Atom c → Literal c
  𝓁Literal    : ℒ c → Literal c

data Clause (c : 𝒞) : Set where
  _:-_ : Atom c
       → List (Literal c)
       → Clause c

data HasVariables : Set where
  expr     : (c : 𝒞) → HasVariables
  domainConstraint   : (c : 𝒞) → HasVariables
  atom        : (c : 𝒞) → HasVariables
  literal     : (c : 𝒞) → HasVariables
  clause      : (c : 𝒞) → HasVariables
  listOf      : HasVariables → HasVariables
  domainExpr    : (c : 𝒞) → HasVariables

⟦_⟧ᵥ : HasVariables → Set
⟦ expr c ⟧ᵥ   = Expr c
⟦ domainConstraint c ⟧ᵥ = ℒ c
⟦ atom c ⟧ᵥ      = Atom c
⟦ literal c ⟧ᵥ   = Literal c
⟦ clause c ⟧ᵥ    = Clause c
⟦ listOf c ⟧ᵥ    = List (⟦ c ⟧ᵥ)
⟦ domainExpr c ⟧ᵥ  = LogicVar (⟦ c ⟧₍𝑑₎ LogicVar)

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

sameLength : ∀ {A B : Set} → List A → List B → Bool
sameLength []       []       = true
sameLength (_ ∷ xs) (_ ∷ ys) = sameLength xs ys
sameLength _        _        = false

Subst : 𝒞 → Set
Subst c = List (ℕ × (LogicVar (⟦ c ⟧₍𝑑₎ LogicVar)))

{-# TERMINATING #-}
applyInTerm : ℕ → LogicVar (Term LogicVar) → Term LogicVar → Term LogicVar
applyInLogicVar : ℕ → LogicVar (Term LogicVar) → LogicVar (Term LogicVar) → LogicVar (Term LogicVar)

applyInTerm x te (atomT head args) = atomT head (Data.List.map (applyInLogicVar x te) args)

applyInLogicVar x te (var nothing) = var nothing
applyInLogicVar x te (var (just y)) with x ≡ᵇ y
... | true = te
... | false = var (just y)
applyInLogicVar x te (const t) = const (applyInTerm x te t)

{-# TERMINATING #-}
applyᵥ : {c : 𝒞} {hv : HasVariables} → ℕ → LogicVar (⟦ c ⟧₍𝑑₎ LogicVar) → ⟦ hv ⟧ᵥ → ⟦ hv ⟧ᵥ

applyᵥ {term} {domainExpr term} = applyInLogicVar

applyᵥ {_} {expr _} k te (domainExpr t) = domainExpr (applyᵥ k te t)

applyᵥ {_} {domainConstraint _} k te (e₁ =ℒ e₂) = applyᵥ k te e₁ =ℒ applyᵥ k te e₂

applyᵥ {_} {atom _} k te (mkAtom s args) =
  mkAtom s (applyᵥ k te args)

applyᵥ {_} {literal _} k te (atomLiteral a) = atomLiteral (applyᵥ k te a)
applyᵥ {_} {literal _} k te (𝓁Literal ℓ)    = 𝓁Literal (applyᵥ k te ℓ)

applyᵥ {_} {clause _} k te (head :- body) =
  applyᵥ k te head :- Data.List.map (applyᵥ k te) body

applyᵥ {_} {listOf _} k te xs =
  Data.List.map (applyᵥ k te) xs

{-# TERMINATING #-}
occursInTerm : ℕ → Term LogicVar → Bool
occursInLogicVar : ℕ → LogicVar (Term LogicVar) → Bool

occursInTerm x (atomT _ args) = any (occursInLogicVar x) args

occursInLogicVar x (var nothing) = false
occursInLogicVar x (var (just y)) = x ≡ᵇ y
occursInLogicVar x (const t) = occursInTerm x t

{-# TERMINATING #-}
occursᵥ : {hv : HasVariables} → ℕ → ⟦ hv ⟧ᵥ → Bool

occursᵥ {domainExpr term} = occursInLogicVar

occursᵥ {expr _} k (domainExpr t) = occursᵥ k t

occursᵥ {domainConstraint _} k (e₁ =ℒ e₂) = occursᵥ k e₁ ∨ occursᵥ k e₂

occursᵥ {atom _} k (mkAtom s args) = occursᵥ k args

occursᵥ {literal _} k (atomLiteral a) = occursᵥ k a
occursᵥ {literal _} k (𝓁Literal ℓ)    = occursᵥ k ℓ

occursᵥ {clause _} k (head :- body) =
  occursᵥ k head ∨ any (occursᵥ k) body

occursᵥ {listOf _} k xs =
  any (occursᵥ k) xs

toSubst : {c : 𝒞} (right : List (ℒ c)) → Subst c
toSubst ((domainExpr (var (just x)) =ℒ domainExpr t) ∷ xs) = (x , t) ∷ toSubst xs
-- hack
toSubst _ = []

{-# TERMINATING #-}
fix : (A : Set) → (A → A) → A
fix A f = f (fix A f)

-- Implementation of Algorithm 1 in "An Efficient Unification Algorithm" by A. Martelli & U. Montanari

{-# TERMINATING #-}
unifyAcc : List (ℒ term) → List (ℒ term) → Maybe (Subst term)
unifyCaseB : List (ℒ term) → List (ℒ term) → Maybe (Maybe (Subst term))
unifyCaseD : List (ℒ term) → List (ℒ term) → Maybe (Maybe (Subst term))

unifyAcc acc [] = just (toSubst acc)
unifyAcc acc ((domainExpr (const t) =ℒ domainExpr (var x)) ∷ xs) = unifyAcc [] (acc ++ (domainExpr (var x) =ℒ domainExpr (const t)) ∷ xs)
unifyAcc acc ((domainExpr (const (atomT root₀ args₀)) =ℒ domainExpr (const (atomT root₁ args₁))) ∷ xs) with (root₀ == root₁) ∧ (sameLength args₀ args₁)
... | true = unifyAcc [] (acc ++ ((zipWith (λ x y → (domainExpr x =ℒ domainExpr y)) args₀ args₁) ++ xs))
... | false = nothing
unifyAcc acc (rightHead ∷ rightTail) with unifyCaseD acc (rightHead ∷ rightTail)
... | just ans = ans
... | nothing with unifyCaseB acc (rightHead ∷ rightTail)
... | just ans = ans
... | nothing = unifyAcc ((rightHead) ∷ acc) rightTail

unifyCaseB acc ((domainExpr (var (just x)) =ℒ domainExpr (var (just y))) ∷ xs) with x ≡ᵇ y
... | true = just (unifyAcc [] (acc ++ xs))
... | false = nothing
unifyCaseB acc ((domainExpr (var (just x)) =ℒ domainExpr (var nothing)) ∷ xs) = just (unifyAcc [] (acc ++ xs))
unifyCaseB acc ((domainExpr (var nothing) =ℒ domainExpr (var (just y))) ∷ xs) = just (unifyAcc [] (acc ++ xs))
unifyCaseB acc ((domainExpr (var nothing) =ℒ domainExpr (var nothing)) ∷ xs) = just (unifyAcc [] (acc ++ xs))
unifyCaseB acc _ = nothing

equalVar : LogicVar (Term LogicVar) → LogicVar (Term LogicVar) → Bool
equalVar (var (just x)) (var (just y)) = x ≡ᵇ y
equalVar _ _ = false

unifyCaseD acc ((domainExpr (var (just x)) =ℒ domainExpr t) ∷ xs) with occursᵥ x (acc ++ xs) ∧ not (equalVar (var (just x)) t)
... | false = nothing
... | true with occursᵥ x t
... | true = just nothing
... | false = just (unifyAcc [] ((applyᵥ x t acc) ++ (domainExpr (var (just x)) =ℒ domainExpr t) ∷ (applyᵥ x t xs)))
unifyCaseD acc ((domainExpr (var nothing) =ℒ domainExpr t) ∷ xs) = nothing
unifyCaseD acc _ = nothing

unify : (right : List (ℒ term)) → Maybe (Subst term)
unify right = unifyAcc [] right

unifyUnitTest0 : 
  (unify (
      (domainExpr (var (just 3)) =ℒ domainExpr (const (atomT "bob" [])))
    ∷ (domainExpr (var (just 2)) =ℒ domainExpr (const (atomT "alice" [])))
    ∷ (domainExpr (var (just 1)) =ℒ domainExpr (var (just 3)))
    ∷ (domainExpr (const (atomT "alice" [])) =ℒ domainExpr (var (just 2)))
    ∷ []) ≡ 
      just (
      (3 , const (atomT "bob" []))
    ∷ (2 , const (atomT "alice" []))
    ∷ (1 , const (atomT "bob" []))
    ∷ []))
unifyUnitTest0 = refl

solve : {c : 𝒞} (right : List (ℒ c)) → ((length right ≡ᵇ 0) ≡ false) → Subst c → Maybe (Subst c)
solve {term} (first ∷ right) refl _ = unify (first ∷ right)

_⇔_ : ∀ {c : 𝒞} → Atom c → Clause c → Bool
mkAtom name₀ args₀ ⇔ (mkAtom name₁ args₁ :- _) = (name₀ == name₁) ∧ (sameLength args₀ args₁)

{-# TERMINATING #-}
incrementLogicVar : ℕ → LogicVar (Term LogicVar) → LogicVar (Term LogicVar)
incrementTerm : ℕ → Term LogicVar → Term LogicVar

incrementLogicVar k (var nothing)    = var nothing
incrementLogicVar k (var (just n))   = var (just (n + k))
incrementLogicVar k (const t)        = const (incrementTerm k t)

incrementTerm k (atomT s args)    = atomT s (Data.List.map (incrementLogicVar k) args)

maybeMax : Maybe ℕ → Maybe ℕ → Maybe ℕ
maybeMax nothing  y         = y
maybeMax x        nothing   = x
maybeMax (just x) (just y)  = just (x Data.Nat.⊔ y)

maxVarLogicVarTerm : LogicVar (Term LogicVar) → Maybe ℕ
maxVarTerm : Term LogicVar → Maybe ℕ
maxVarLogicVars : List (LogicVar (Term LogicVar)) → Maybe ℕ

maxVarLogicVarTerm (var nothing) = nothing
maxVarLogicVarTerm (var (just x)) = just x
maxVarLogicVarTerm (const t) = maxVarTerm t

maxVarTerm (atomT _ args) = maxVarLogicVars args

maxVarLogicVars [] = nothing
maxVarLogicVars (x ∷ xs) = maybeMax (maxVarLogicVarTerm x) (maxVarLogicVars xs)

{-# TERMINATING #-}
incrementLogicVarTerm : ℕ → LogicVar (Term LogicVar) → LogicVar (Term LogicVar)
incrementLogicVarTerm k (var nothing) = var nothing
incrementLogicVarTerm k (var (just x)) = var (just (x + k))
incrementLogicVarTerm k (const t) = const (mapTerm (incrementLogicVarTerm k) t)

{-# TERMINATING #-}
incrementᵥ : {hv : HasVariables} → ℕ → ⟦ hv ⟧ᵥ → ⟦ hv ⟧ᵥ

incrementᵥ {domainExpr term} = incrementLogicVarTerm

incrementᵥ {expr _} k (domainExpr t) = domainExpr (incrementᵥ k t)

incrementᵥ {domainConstraint _} k (e₁ =ℒ e₂) = incrementᵥ k e₁ =ℒ incrementᵥ k e₂

incrementᵥ {atom _} k (mkAtom s args) =
  mkAtom s (incrementᵥ k args)

incrementᵥ {literal _} k (atomLiteral a) = atomLiteral (incrementᵥ k a)
incrementᵥ {literal _} k (𝓁Literal ℓ)    = 𝓁Literal (incrementᵥ k ℓ)

incrementᵥ {clause _} k (head :- body) =
  incrementᵥ k head :- Data.List.map (incrementᵥ k) body

incrementᵥ {listOf _} k xs =
  Data.List.map (incrementᵥ k) xs

maxVarᵥ : {hv : HasVariables} → ⟦ hv ⟧ᵥ → Maybe ℕ

maxVarᵥ {domainExpr term} = maxVarLogicVarTerm

maxVarᵥ {expr _} (domainExpr t) = maxVarᵥ t

maxVarᵥ {domainConstraint _} (e₁ =ℒ e₂) = maybeMax (maxVarᵥ e₁) (maxVarᵥ e₂)

maxVarᵥ {atom _} (mkAtom _ args) =
  maxVarᵥ args

maxVarᵥ {literal _} (atomLiteral a) = maxVarᵥ a
maxVarᵥ {literal _} (𝓁Literal ℓ)    = maxVarᵥ ℓ

maxVarᵥ {clause _} (head :- body) =
  maybeMax (maxVarᵥ head) (maxVarᵥ body)

maxVarᵥ {listOf _} []       = nothing
maxVarᵥ {listOf _} (x ∷ xs) = maybeMax (maxVarᵥ x) (maxVarᵥ xs)

-- use maybe monad
bindAndRename : {c : 𝒞} → Atom c → Maybe ℕ → Clause c → List (Literal c)
bindAndRename {c} (mkAtom _ exprs₀) nothing  (mkAtom _ exprs₁ :- l) = 
  zipWith (λ x y → 𝓁Literal (x =ℒ y)) exprs₀ exprs₁ ++ l
bindAndRename {c} (mkAtom _ exprs₀) (just n) (mkAtom _ exprs₁ :- l) = 
  zipWith (λ x y → 𝓁Literal (x =ℒ y)) exprs₀ (incrementᵥ (suc n) exprs₁) ++ incrementᵥ (suc n) l

removeUnusedVars : {c : 𝒞} → List (Literal c) → Subst c → Subst c
removeUnusedVars right [] = []
removeUnusedVars right ((x , t) ∷ xs) with occursᵥ x right
... | true = (x , t) ∷ (removeUnusedVars right xs)
... | false = removeUnusedVars right xs

{-# TERMINATING #-}
eval : 
  {c : 𝒞}
  → List (Clause c)
  → List (Literal c)
  → List (ℒ c)
  → (findAll : Bool)
  → Subst c
  → if findAll then List (Subst c) else Maybe (Subst c)

eval program [] right true subst = subst ∷ []
eval program [] right false subst = just subst

eval     program         (atomLiteral at ∷ left) right _ _ with findAll ((_⇔_) at) program
eval {c} .(forget split) (atomLiteral at ∷ left) right false subst | matches split _ _ 
  with Data.List.map (λ {cl → 
    Data.Maybe.map
      (removeUnusedVars (atomLiteral at ∷ left ++ Data.List.map 𝓁Literal right)) 
        (eval
          (forget split)
          ((bindAndRename at (maybeMax (maxVarᵥ (atomLiteral at ∷ left)) (maxVarᵥ right)) cl) ++ left)
          right
          false
          subst)})
      (first split)

eval {c} .(forget split) (atomLiteral at ∷ left) right false _ | matches split _ _
  | derivations with find (λ {(just _) → true ; nothing → false}) derivations
eval     .(forget split) (atomLiteral at ∷ left) right _ _ | matches split _ _
  | .(_ ++ successful-derivation ∷ _) | found before successful-derivation _ after = successful-derivation
eval     .(forget split)        (atomLiteral at ∷ left) right _ _ | matches split _ _
  | no-successful-derivations         | not-found _ = nothing

eval {c} .(forget split) (atomLiteral at ∷ left) right true subst | matches split _ _ 
  with Data.List.map (λ {cl → 
    Data.List.map
      (removeUnusedVars (atomLiteral at ∷ left ++ Data.List.map 𝓁Literal right)) 
        (eval
          (forget split)
          ((bindAndRename at (maybeMax (maxVarᵥ (atomLiteral at ∷ left)) (maxVarᵥ right)) cl) ++ left)
          right
          true
          subst)})
      (first split)
eval {c} .(forget split) (atomLiteral at ∷ left) right true _ | matches split _ _
  | derivations with findAll (λ {(_ ∷ _) → true ; [] → false}) derivations
eval     .(forget split) (atomLiteral at ∷ left) right _ _ | matches split _ _
  | .(forget splitNondet) | matches splitNondet _ _ = concat (first splitNondet)

eval program (𝓁Literal cnstr ∷ left) right false subst with solve (cnstr ∷ right) refl subst
eval program (𝓁Literal cnstr ∷ left) right false subst | just newSubst = eval program left (cnstr ∷ right) false newSubst
eval program (𝓁Literal cnstr ∷ left) right false subst | nothing = nothing

eval program (𝓁Literal cnstr ∷ left) right true subst with solve (cnstr ∷ right) refl subst
eval program (𝓁Literal cnstr ∷ left) right true subst | just newSubst = eval program left (cnstr ∷ right) true newSubst
eval program (𝓁Literal cnstr ∷ left) right true subst | nothing = []

ancestor_program : List (Clause term)
ancestor_program =
    (mkAtom "parent"
  (domainExpr (const (atomT "alice" [])) ∷
    domainExpr (const (atomT "bob" [])) ∷ [])
  :- [])
  ∷
  (mkAtom "parent"
  (domainExpr (const (atomT "bob" [])) ∷
    domainExpr (const (atomT "charlie" [])) ∷ [])
  :- [])
  ∷
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷ domainExpr (var (just 2)) ∷ [])
  :-
  (atomLiteral
    (mkAtom "parent"
    (domainExpr (var (just 1)) ∷ domainExpr (var (just 2)) ∷ []))
    ∷ []))
  ∷
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷ domainExpr (var (just 2)) ∷ [])
  :-
  (atomLiteral
    (mkAtom "parent"
    (domainExpr (var (just 1)) ∷ domainExpr (var (just 3)) ∷ []))
    ∷
    atomLiteral
    (mkAtom "ancestor"
    (domainExpr (var (just 3)) ∷ domainExpr (var (just 2)) ∷ []))
    ∷ []))
  ∷ []

evalUnitTest0 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (const (atomT "charlie" [])) ∷ []))
  ∷ []) [] false [] ≡ just (( 1 , const (atomT "bob" []) ) ∷ []))
evalUnitTest0 = refl

evalUnitTest1 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (const (atomT "charlie" [])) ∷ []))
  ∷ []) [] true [] ≡ ((( 1 , const (atomT "bob" []) ) ∷ []) ∷ (( 1 , const (atomT "alice" []) ) ∷ []) ∷ []))
evalUnitTest1 = refl

evalUnitTest2 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (var (just 2)) ∷ []))
  ∷ []) [] false [] ≡ just (( 1 , const (atomT "alice" []) ) ∷ ( 2 , const (atomT "bob" [])) ∷ []))
evalUnitTest2 = refl

evalUnitTest3 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (var (just 2)) ∷ []))
  ∷ []) [] true [] ≡ (( 1 , const (atomT "alice" []) ) ∷ ( 2 , const (atomT "bob" [])) ∷ [])
   ∷ (( 1 , const (atomT "bob" []) ) ∷ ( 2 , const (atomT "charlie" [])) ∷ [])
   ∷ (( 1 , const (atomT "alice" []) ) ∷ ( 2 , const (atomT "charlie" [])) ∷ []) ∷ [])
evalUnitTest3 = refl

mutual
  data LogicVarForHs : Set where
    varForHs : Maybe ℕ → LogicVarForHs
    constForHs : TermForHs → LogicVarForHs

  data TermForHs : Set where
    atomTForHs : String → List LogicVarForHs → TermForHs

data ExprTerm : Set where
  domainExprTerm : LogicVarForHs → ExprTerm

data AtomTerm : Set where
  mkAtomTerm : String → List ExprTerm → AtomTerm

data ℒTerm : Set where
  eqTerm : ExprTerm → ExprTerm → ℒTerm

data LiteralTerm : Set where
  atomLiteralTerm : AtomTerm → LiteralTerm
  eqLiteralTerm   : ℒTerm → LiteralTerm

data ClauseTerm : Set where
  mkClauseTerm : AtomTerm → List LiteralTerm → ClauseTerm

{-# TERMINATING #-}
fromLogicVarForHs : LogicVarForHs → LogicVar (Term LogicVar)
fromTermForHs : TermForHs → Term LogicVar

fromLogicVarForHs (varForHs x) = var x
fromLogicVarForHs (constForHs t) = const (fromTermForHs t)

fromTermForHs (atomTForHs s args) = atomT s (Data.List.map fromLogicVarForHs args)

fromExprTerm : ExprTerm → Expr term
fromExprTerm (domainExprTerm x) = domainExpr (fromLogicVarForHs x)

fromAtomTerm : AtomTerm → Atom term
fromAtomTerm (mkAtomTerm name args) = mkAtom name (Data.List.map fromExprTerm args)

fromℒTerm : ℒTerm → ℒ term
fromℒTerm (eqTerm e₁ e₂) = fromExprTerm e₁ =ℒ fromExprTerm e₂

fromLiteralTerm : LiteralTerm → Literal term
fromLiteralTerm (atomLiteralTerm a) = atomLiteral (fromAtomTerm a)
fromLiteralTerm (eqLiteralTerm l)   = 𝓁Literal (fromℒTerm l)

fromClauseTerm : ClauseTerm → Clause term
fromClauseTerm (mkClauseTerm head body) = fromAtomTerm head :- Data.List.map fromLiteralTerm body

data SubstTerm : Set where
  substTerm : ℕ → LogicVarForHs → SubstTerm

data EvalTerm : Set where
  yesAllTerm : List (List SubstTerm) → EvalTerm
  yesTerm : List SubstTerm → EvalTerm
  noTerm  : EvalTerm

{-# TERMINATING #-}
toLogicVarForHs : LogicVar (Term LogicVar) → LogicVarForHs
toTermForHs : Term LogicVar → TermForHs

toLogicVarForHs (var x)     = varForHs x
toLogicVarForHs (const tm)  = constForHs (toTermForHs tm)

toTermForHs (atomT s args)  = atomTForHs s (Data.List.map toLogicVarForHs args)

toSubstTerm : Subst term → List SubstTerm
toSubstTerm subst = Data.List.map (λ (x , y) → substTerm x (toLogicVarForHs y)) subst

toEvalTerm : {findAll : Bool} → if findAll then List (Subst term) else Maybe (Subst term) → EvalTerm
toEvalTerm {false} (just subst) = yesTerm (toSubstTerm subst)
toEvalTerm {true} subst = yesAllTerm (Data.List.map toSubstTerm subst)
toEvalTerm {false} nothing      = noTerm

evalTerm : (program : List (ClauseTerm)) → (left : List (LiteralTerm)) → Bool → EvalTerm
evalTerm program left findAll = toEvalTerm (eval (Data.List.map fromClauseTerm program) (Data.List.map fromLiteralTerm left) [] findAll [])

{-# FOREIGN GHC {-# LANGUAGE DeriveDataTypeable #-} #-}

{-# FOREIGN GHC
  import Data.Data (Data)
  import Data.Typeable (Typeable)
  import Data.Text (Text)

  data TermHs
    = MkAtomTHs Text [LogicVarHs]
    deriving (Show, Eq, Data, Typeable)

  data LogicVarHs
    = MkVarHs (Maybe Integer)
    | MkConstHs TermHs
    deriving (Show, Eq, Data, Typeable)

  -- ExprTerm
  data ExprTermHs
    = MkExprTermHs LogicVarHs
    deriving (Show, Eq, Data, Typeable)

  -- AtomTerm
  data AtomTermHs
    = MkAtomTermHs Text [ExprTermHs]
    deriving (Show, Eq, Data, Typeable)

  -- ℒTerm
  data ℒTerm
    = EqTermHs ExprTermHs ExprTermHs
    deriving (Show, Eq, Data, Typeable)

  -- LiteralTerm
  data LiteralTermHs
    = AtomLiteralTermHs AtomTermHs
    | EqLiteralTermHs ℒTerm
    deriving (Show, Eq, Data, Typeable)

  -- ClauseTerm
  data ClauseTermHs
    = MkClauseTermHs AtomTermHs [LiteralTermHs]
    deriving (Show, Eq, Data, Typeable)

  -- SubstTerm
  data SubstTermHs
    = SubstTermHs Integer LogicVarHs
    deriving (Show, Eq, Data, Typeable)

  -- EvalTerm
  data EvalTermHs
    = YesAllTermHs [[SubstTermHs]]
    | YesTermHs [SubstTermHs]
    | NoTermHs
    deriving (Show, Eq, Data, Typeable)
#-}

{-# COMPILE GHC TermForHs = data TermHs (MkAtomTHs) #-}
{-# COMPILE GHC LogicVarForHs = data LogicVarHs (MkVarHs | MkConstHs) #-}
{-# COMPILE GHC ExprTerm = data ExprTermHs (MkExprTermHs) #-}
{-# COMPILE GHC AtomTerm = data AtomTermHs (MkAtomTermHs) #-}
{-# COMPILE GHC ℒTerm = data ℒTerm (EqTermHs) #-}
{-# COMPILE GHC LiteralTerm = data LiteralTermHs (AtomLiteralTermHs | EqLiteralTermHs) #-}
{-# COMPILE GHC ClauseTerm = data ClauseTermHs (MkClauseTermHs) #-}
{-# COMPILE GHC SubstTerm = data SubstTermHs (SubstTermHs) #-}
{-# COMPILE GHC EvalTerm = data EvalTermHs (YesAllTermHs | YesTermHs | NoTermHs) #-}

{-# COMPILE GHC evalTerm as evalTermAgda #-}
-- eval my_last my_last_question [] []
-- TO DO:
-- All / First
-- Unit Tests
-- Haskell anbindung + Parser
-- wildcard checker
-- In files (modules) aufteilen
-- Github
-- Dokumentation im Readme
-- Mail