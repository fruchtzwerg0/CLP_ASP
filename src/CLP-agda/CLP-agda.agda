module CLP-agda where

open import Data.String 
  using (String; _==_)
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst)
open import Data.List 
  using (List; []; _∷_; _++_; any; all; map; foldl; length; zip; zipWith)
open import Data.Bool
open import Data.Nat 
  using (ℕ; _≡ᵇ_; _⊔_; _⊓_; _+_)
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

data Type (a : Set) : Set where
  var : Maybe ℕ → Type a
  const : a → Type a

{-# NO_POSITIVITY_CHECK #-}
data Term (f : Set → Set) : Set where
  constT : String → Term f
  atomT : String → List (f (Term f)) → Term f

TypeTerm : Set
TypeTerm = Type (Term Type)

{-# TERMINATING #-}
mapTypeTerm : (TypeTerm → TypeTerm) → TypeTerm → TypeTerm
mapTerm : (TypeTerm → TypeTerm) → Term Type → Term Type

mapTypeTerm f (var x) = f (var x)
mapTypeTerm f (const t) = const (mapTerm f t)

mapTerm f (constT s) = constT s
mapTerm f (atomT s args) = atomT s (Data.List.map (mapTypeTerm f) args)

data 𝒞 : Set where
  term : 𝒞

⟦_⟧₍𝑑₎ : 𝒞 → Set
⟦ term ⟧₍𝑑₎ = Type (Term Type)

mapJust : {A : Set} → (A → A → A) → Maybe A → Maybe A → Maybe A
mapJust f (just n) (just m) = just (f n m)
mapJust _ (just n) nothing = just n
mapJust _ nothing x = x

data Expr : 𝒞 → Set where
  domainExpr : {c : 𝒞} → ⟦ c ⟧₍𝑑₎ → Expr c

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

data HasVariables : Set₁ where
  exprType     : (c : 𝒞) → HasVariables
  domainConstraint   : (c : 𝒞) → HasVariables
  atom        : (c : 𝒞) → HasVariables
  literal     : (c : 𝒞) → HasVariables
  clause      : (c : 𝒞) → HasVariables
  listOf      : HasVariables → HasVariables
  typed       : (c : 𝒞) → HasVariables

⟦_⟧ᵥ : HasVariables → Set
⟦ exprType c ⟧ᵥ   = Expr c
⟦ domainConstraint c ⟧ᵥ = ℒ c
⟦ atom c ⟧ᵥ      = Atom c
⟦ literal c ⟧ᵥ   = Literal c
⟦ clause c ⟧ᵥ    = Clause c
⟦ listOf c ⟧ᵥ    = List (⟦ c ⟧ᵥ)
⟦ typed c ⟧ᵥ     = ⟦ c ⟧₍𝑑₎

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

Subst : 𝒞 → Set
Subst c = List (ℕ × ⟦ c ⟧₍𝑑₎)

data Eval (c : 𝒞) : Set where
  yes : (subst : Subst c) → Eval c
  no  : Eval c

-- Result type of unification
data Unify? : Type (Term Type) → Type (Term Type) → Set where
  yes : ∀ {t₁ t₂} → Subst term → Unify? t₁ t₂
  no  : ∀ {t₁ t₂} → Unify? t₁ t₂

-- Lookup
lookup : ℕ → Subst term → Maybe (Type (Term Type))
lookup x [] = nothing
lookup x ((y , t) ∷ σ) with x ≡ᵇ y
... | true  = just t
... | false = lookup x σ

-- Apply substitution to Type (Term Type)
{-# TERMINATING #-}
apply : Subst term → Type (Term Type) → Type (Term Type)
apply σ (var nothing) = var nothing
apply σ (var (just x)) with lookup x σ
... | just t  = t
... | nothing = var (just x)
apply σ (const t) = const (mapTerm (apply σ) t)

{-# TERMINATING #-}
occursInTerm : ℕ → Term Type → Bool
occursInType : ℕ → Type (Term Type) → Bool

occursInTerm x (constT _) = false
occursInTerm x (atomT _ args) = any (occursInType x) args

occursInType x (var nothing) = false
occursInType x (var (just y)) = x ≡ᵇ y
occursInType x (const t) = occursInTerm x t

occurs : ℕ → Type (Term Type) → Bool
occurs x (var nothing) = false
occurs x (var (just y)) = x ≡ᵇ y
occurs x (const t) = occursInTerm x t

-- Bind a variable
bindVar : ℕ → Type (Term Type) → Maybe (Subst term)
bindVar x t with occurs x t
... | true  = nothing
... | false = just ((x , t) ∷ [])

-- Compose substitutions
compose : Subst term → Subst term → Subst term
compose σ₁ σ₂ =
  let σ₂′ = Data.List.map (λ (x , t) → (x , apply σ₁ t)) σ₂
  in σ₂′ ++ σ₁

-- Unify list of arguments
{-# TERMINATING #-}
unifyArgs : List (Type (Term Type) × Type (Term Type)) → Subst term → Maybe (Subst term)
unify : Type (Term Type) → Type (Term Type) → Subst term → Maybe (Subst term)
unifyTerm : Term Type → Term Type → Subst term → Maybe (Subst term)
unifyCore : Type (Term Type) → Type (Term Type) → Subst term → Maybe (Subst term)

unifyArgs [] σ = just σ
unifyArgs ((t₁ , t₂) ∷ rest) σ with unify t₁ t₂ σ
... | nothing = nothing
... | just σ′ = unifyArgs rest σ′

unify t₁ t₂ σ =
  let lhs = apply σ t₁
      rhs = apply σ t₂
  in unifyCore lhs rhs σ

unifyTerm (constT s₁) (constT s₂) σ with s₁ == s₂
... | true  = just σ
... | false = nothing

unifyTerm (atomT f₁ args₁) (atomT f₂ args₂) σ with f₁ == f₂ | zip args₁ args₂
... | false | _ = nothing
... | true | zipped = unifyArgs zipped σ

unifyTerm _ _ _ = nothing

unifyCore (var (just x)) t σ with occurs x t
... | true  = nothing
... | false = just ((x , t) ∷ σ)

unifyCore t (var (just x)) σ with occurs x t
... | true  = nothing
... | false = just ((x , t) ∷ σ)

-- Wildcards unify trivially, don’t affect subst
unifyCore (var nothing) _ σ = just σ
unifyCore _ (var nothing) σ = just σ

unifyCore (const t₁) (const t₂) σ = unifyTerm t₁ t₂ σ
-- unifyCore _ _ _ = nothing

solve : {c : 𝒞} (right : List (ℒ c)) → ((length right ≡ᵇ 0) ≡ false) → Subst c → Eval c
solve {term} ((domainExpr t₁ =ℒ domainExpr t₂) ∷ _) refl σ with unify t₁ t₂ σ
... | just σ′ = yes (σ′ ++ σ)
... | nothing = no

sameLength : ∀ {A B : Set} → List A → List B → Bool
sameLength []       []       = true
sameLength (_ ∷ xs) (_ ∷ ys) = sameLength xs ys
sameLength _        _        = false

_⇔_ : ∀ {c : 𝒞} → Atom c → Clause c → Bool
mkAtom name₀ args₀ ⇔ (mkAtom name₁ args₁ :- _) = (name₀ == name₁) ∧ (sameLength args₀ args₁)

{-# TERMINATING #-}
incrementType : ℕ → Type (Term Type) → Type (Term Type)
incrementTerm : ℕ → Term Type → Term Type

incrementType k (var nothing)    = var nothing
incrementType k (var (just n))   = var (just (n + k))
incrementType k (const t)        = const (incrementTerm k t)

incrementTerm k (constT s)        = constT s
incrementTerm k (atomT s args)    = atomT s (Data.List.map (incrementType k) args)

maybeMax : Maybe ℕ → Maybe ℕ → Maybe ℕ
maybeMax nothing  y         = y
maybeMax x        nothing   = x
maybeMax (just x) (just y)  = just (x Data.Nat.⊔ y)

maxVarTypeTerm : Type (Term Type) → Maybe ℕ
maxVarTerm : Term Type → Maybe ℕ
maxVarTypes : List (Type (Term Type)) → Maybe ℕ

maxVarTypeTerm (var nothing) = nothing
maxVarTypeTerm (var (just x)) = just x
maxVarTypeTerm (const t) = maxVarTerm t

maxVarTerm (constT _) = nothing
maxVarTerm (atomT _ args) = maxVarTypes args

maxVarTypes [] = nothing
maxVarTypes (x ∷ xs) = maybeMax (maxVarTypeTerm x) (maxVarTypes xs)

{-# TERMINATING #-}
incrementTypeTerm : ℕ → Type (Term Type) → Type (Term Type)
incrementTypeTerm k (var nothing) = var nothing
incrementTypeTerm k (var (just x)) = var (just (x + k))
incrementTypeTerm k (const t) = const (mapTerm (incrementTypeTerm k) t)

{-# TERMINATING #-}
incrementᵥ : ∀ (hv : HasVariables) → ℕ → ⟦ hv ⟧ᵥ → ⟦ hv ⟧ᵥ

incrementᵥ (typed term) = incrementTypeTerm

incrementᵥ (exprType c) k (domainExpr t) = domainExpr (incrementᵥ (typed c) k t)

incrementᵥ (domainConstraint c) k (e₁ =ℒ e₂) = incrementᵥ (exprType c) k e₁ =ℒ incrementᵥ (exprType c) k e₂

incrementᵥ (atom c) k (mkAtom s args) =
  mkAtom s (incrementᵥ (listOf (exprType c)) k args)

incrementᵥ (literal c) k (atomLiteral a) = atomLiteral (incrementᵥ (atom c) k a)
incrementᵥ (literal c) k (𝓁Literal ℓ)    = 𝓁Literal (incrementᵥ (domainConstraint c) k ℓ)

incrementᵥ (clause c) k (head :- body) =
  incrementᵥ (atom c) k head :- Data.List.map (incrementᵥ (literal c) k) body

incrementᵥ (listOf a) k xs =
  Data.List.map (incrementᵥ a k) xs

maxVarᵥ : ∀ (hv : HasVariables) → ⟦ hv ⟧ᵥ → Maybe ℕ

maxVarᵥ (typed term) = maxVarTypeTerm

maxVarᵥ (exprType c) (domainExpr t) = maxVarᵥ (typed c) t

maxVarᵥ (domainConstraint c) (e₁ =ℒ e₂) = maybeMax (maxVarᵥ (exprType c) e₁) (maxVarᵥ (exprType c) e₂)

maxVarᵥ (atom c) (mkAtom _ args) =
  maxVarᵥ (listOf (exprType c)) args

maxVarᵥ (literal c) (atomLiteral a) = maxVarᵥ (atom c) a
maxVarᵥ (literal c) (𝓁Literal ℓ)    = maxVarᵥ (domainConstraint c) ℓ

maxVarᵥ (clause c) (head :- body) =
  maybeMax (maxVarᵥ (atom c) head) (maxVarᵥ (listOf (literal c)) body)

maxVarᵥ (listOf a) []       = nothing
maxVarᵥ (listOf a) (x ∷ xs) = maybeMax (maxVarᵥ a x) (maxVarᵥ (listOf a) xs)

bindAndRename : ∀ {c : 𝒞} → Atom c → Maybe ℕ → Clause c → List (Literal c)
bindAndRename _ nothing (_ :- l) = l
bindAndRename {c} (mkAtom _ exprs₀) (just n) (mkAtom _ exprs₁ :- l) = 
    zipWith (λ x y → 𝓁Literal (x =ℒ y)) exprs₀ (incrementᵥ (listOf (exprType c)) n exprs₁) ++ incrementᵥ (listOf (literal c)) n l

{-# TERMINATING #-}
eval : {c : 𝒞} → (program : List (Clause c)) → (left : List (Literal c)) → (right : List (ℒ c)) → Subst c → Eval c

eval program [] right subst = yes subst

eval     program         (atomLiteral at ∷ left) right _ with findAll ((_⇔_) at) program
eval {c} .(forget split) (atomLiteral at ∷ left) right subst | matches split _ _ 
  with Data.List.map (λ {cl → eval (forget split) ((bindAndRename at (maxVarᵥ (listOf (literal c)) left) cl) ++ left) right subst}) (first split)
eval {c} .(forget split) (atomLiteral at ∷ left) right _ | matches split _ _
  | derivations with find (λ {(yes _) → true ; no → false}) derivations
eval     .(forget split) (atomLiteral at ∷ left) right _ | matches split _ _
  | .(_ ++ successful-derivation ∷ _) | found before successful-derivation _ after = successful-derivation
eval     .(forget split)        (atomLiteral at ∷ left) right _ | matches split _ _
  | no-successful-derivations         | not-found _ = no

eval program (𝓁Literal cnstr ∷ left) right subst with solve (cnstr ∷ right) refl subst
eval program (𝓁Literal cnstr ∷ left) right subst | yes newSubst = eval program left (cnstr ∷ right) newSubst
eval program (𝓁Literal cnstr ∷ left) right subst | no = no

-- eval-subst-num-equal-to-var-num-in-goal : {c : 𝒞} → (program : List (Clause c)) → (left : List (Literal c)) →  → (eval program left [] [])

-- my_last(X,[X]).
-- my_last(X,[_|L]) :- my_last(X,L).
my_last : List (Clause term)
my_last = 
  mkAtom "my_last" (domainExpr (var (just 0)) ∷ domainExpr (const (atomT "cons" ((var (just 0)) ∷ (const (constT "[]")) ∷ []))) ∷ []) :- [] ∷
  mkAtom "my_last"
  ( domainExpr (var (just 0)) ∷
    domainExpr (const (atomT "cons"
      ( var nothing ∷ var (just 1) ∷ [] ))) ∷ [] )
  :- (atomLiteral (mkAtom "my_last" (domainExpr (var (just 0)) ∷ domainExpr (var (just 1)) ∷ [])) ∷ []) ∷ []

-- ?- my_last(X,[a,b,c,d]).
my_last_question : List (Literal term)
my_last_question = 
  atomLiteral (mkAtom "my_last" (domainExpr (var (just 0)) ∷ domainExpr (const (atomT "cons" ((const (constT "a") ∷ (const (atomT "cons" ((const (constT "b") ∷ (const (atomT "cons" ((const (constT "c") ∷ (const (atomT "cons" ((const (constT "d") ∷ (const (constT "[]")) ∷ [])))) ∷ [])))) ∷ [])))) ∷ [])))) ∷ [])) ∷ []

mutual
  data TypeForHs : Set where
    varForHs : Maybe ℕ → TypeForHs
    constForHs : TermForHs → TypeForHs

  data TermForHs : Set where
    constTForHs : String → TermForHs
    atomTForHs : String → List TypeForHs → TermForHs

data ExprTerm : Set where
  domainExprTerm : TypeForHs → ExprTerm

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
fromTypeForHs : TypeForHs → Type (Term Type)
fromTermForHs : TermForHs → Term Type

fromTypeForHs (varForHs x) = var x
fromTypeForHs (constForHs t) = const (fromTermForHs t)

fromTermForHs (constTForHs s) = constT s
fromTermForHs (atomTForHs s args) = atomT s (Data.List.map fromTypeForHs args)

fromExprTerm : ExprTerm → Expr term
fromExprTerm (domainExprTerm x) = domainExpr (fromTypeForHs x)

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
  substTerm : ℕ → TypeForHs → SubstTerm

data EvalTerm : Set where
  yesTerm : List SubstTerm → EvalTerm
  noTerm  : EvalTerm

{-# TERMINATING #-}
toTypeForHs : Type (Term Type) → TypeForHs
toTermForHs : Term Type → TermForHs

toTypeForHs (var x)     = varForHs x
toTypeForHs (const tm)  = constForHs (toTermForHs tm)

toTermForHs (constT s)      = constTForHs s
toTermForHs (atomT s args)  = atomTForHs s (Data.List.map toTypeForHs args)

toSubstTerm : Subst term → List SubstTerm
toSubstTerm subst = Data.List.map (λ (x , y) → substTerm x (toTypeForHs y)) subst

toEvalTerm : Eval term → EvalTerm
toEvalTerm (yes subst) = yesTerm (toSubstTerm subst)
toEvalTerm no          = noTerm

evalTerm : (program : List (ClauseTerm)) → (left : List (LiteralTerm)) → EvalTerm
evalTerm program left = toEvalTerm (eval (Data.List.map fromClauseTerm program) (Data.List.map fromLiteralTerm left) [] [])

{-# FOREIGN GHC
  import Data.Text (Text)

  data TermHs
    = MkConstTHs Text
    | MkAtomTHs Text [TypeHs]

  data TypeHs
    = MkVarHs (Maybe Integer)
    | MkConstHs TermHs

  -- ExprTerm
  data ExprTermHs
    = MkExprTermHs TypeHs

  -- AtomTerm
  data AtomTermHs
    = MkAtomTermHs Text [ExprTermHs]

  -- ℒTerm
  data ℒTerm
    = EqTermHs ExprTermHs ExprTermHs

  -- LiteralTerm
  data LiteralTermHs
    = AtomLiteralTermHs AtomTermHs
    | EqLiteralTermHs ℒTerm

  -- ClauseTerm
  data ClauseTermHs
    = MkClauseTermHs AtomTermHs [LiteralTermHs]

  -- SubstTerm
  data SubstTermHs
    = SubstTermHs Integer TypeHs

  -- EvalTerm
  data EvalTermHs
    = YesTermHs [SubstTermHs]
    | NoTermHs
#-}

{-# COMPILE GHC TermForHs = data TermHs (MkConstTHs | MkAtomTHs) #-}
{-# COMPILE GHC TypeForHs = data TypeHs (MkVarHs | MkConstHs) #-}
{-# COMPILE GHC ExprTerm = data ExprTermHs (MkExprTermHs) #-}
{-# COMPILE GHC AtomTerm = data AtomTermHs (MkAtomTermHs) #-}
{-# COMPILE GHC ℒTerm = data ℒTerm (EqTermHs) #-}
{-# COMPILE GHC LiteralTerm = data LiteralTermHs (AtomLiteralTermHs | EqLiteralTermHs) #-}
{-# COMPILE GHC ClauseTerm = data ClauseTermHs (MkClauseTermHs) #-}
{-# COMPILE GHC SubstTerm = data SubstTermHs (SubstTermHs) #-}
{-# COMPILE GHC EvalTerm = data EvalTermHs (YesTermHs | NoTermHs) #-}

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