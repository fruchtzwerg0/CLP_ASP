module CLP.types where

open import Data.Bool hiding (not ; _∧_)
open import Data.Char
open import Data.String hiding (head; _++_)
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.List hiding (head)
open import Data.Product
open import Data.Sum

open import CLP.ftUtilsDerivation

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Effect.Monad using (RawMonad)
open import Agda.Builtin.String
open import Agda.Builtin.Unit

-- Equality and disequality constraints over a term type A
data ℒ (A : Set) : Set where
  _=ℒ_ : A → A → ℒ A
  _≠ℒ_ : A → A → ℒ A

infixr 80 _=ℒ_
infixr 80 _≠ℒ_

-- A constraint tagged as either the default or its dual
data Dual (A : Set) : Set where
  default : A → Dual A
  dual : A → Dual A

-- Typeclass for generating fresh variables
record MakeVar {l} (A : Set l) : Set l where
  field
    fresh : ℕ → A
    new : A
open MakeVar ⦃...⦄ public

-- Marks whether an atom appears in a rule head or body
data Where : Set where
  headOfRule : Where
  bodyOfRule : Where

-- Forward declaration needed by ConstraintUtils and ValueUtils
record Σᵢ (A : Set) (B : A → Set) (Code : A → Set) (Cns : A → Set) : Set

-- Operations on user-defined constraint types
record ConstraintUtils (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    zipMatch : (c : 𝒞) → Constraint c → Constraint c → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
    increment : (c : 𝒞) → ℕ → Constraint c → Constraint c
    apply : (c₀ : 𝒞) → (c₁ : 𝒞) → ℕ → Code c₀ → Constraint c₁ → Constraint c₁
open ConstraintUtils ⦃...⦄ public

-- Operations on solver-domain value types (terms/codes)
record ValueUtils (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    zipMatch : (c : 𝒞) → Code c → Code c → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
    increment : (c : 𝒞) → ℕ → Code c → Code c
    apply : (c₀ : 𝒞) → (c₁ : 𝒞) → ℕ → Code c₀ → Code c₁ → Code c₁
open ValueUtils ⦃...⦄ public

-- A solver-tagged value: pairs a solver id with a payload of that solver's type
record Σᵢ A B Code Cns where
  constructor _:-:_
  field
    code   : A
    value : B code
    ⦃ instftval ⦄ : FTUtils (Code code)
    ⦃ instftcns ⦄ : FTUtils (Cns code)
    ⦃ decval ⦄ : DecEq (Code code)
    ⦃ makeVar ⦄ : MakeVar (Code code)
    ⦃ showVal ⦄ : Show (Code code)
    ⦃ showCns ⦄ : Show (Cns code)
open Σᵢ public

-- Operations on atom types (used for zipMatch, substitution, increment)
record AtomUtils (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    zipMatch : Atom → Atom → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
    increment : ℕ → Atom → Atom
    apply : (c : 𝒞) → ℕ → Code c → Atom → Atom
open AtomUtils ⦃...⦄ public

-- A value paired with an FTUtils instance for its type
record _×ᵢ_ (A : Set) (B : Set) : Set where
  constructor _<ᵢ
  field
    code    : A
    ⦃ inst ⦄ : FTUtils B
open _×ᵢ_ public

-- A rule body literal: either an atom or a mixed constraint
data Literal 
  (A : Set)
  (𝒞 : Set) 
  (Code : (𝒞 → Set))
  (Constraint : (𝒞 → Set)) : Set where
  atom : ⦃ FTUtils A ⦄ → ⦃ AtomUtils A 𝒞 Code Constraint ⦄ → A → Literal A 𝒞 Code Constraint
  constraint : (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) → Literal A 𝒞 Code Constraint

-- A typed rule body: a snoc-list of atom–value pairs and constraints
data Body 
  (A : Set) 
  (val : A → Set)
  (𝒞 : Set) 
  (Code : (𝒞 → Set))
  (Constraint : (𝒞 → Set)) : Set where
  end  : ⦃ FTUtils A ⦄ → ⦃ AtomUtils A 𝒞 Code Constraint ⦄ → (atom : A) → val atom → Body A val 𝒞 Code Constraint
  endst  : (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) 
            → Body A val 𝒞 Code Constraint
  cons : ⦃ FTUtils A ⦄ → ⦃ AtomUtils A 𝒞 Code Constraint ⦄ → (atom : A) → val atom → Body A val 𝒞 Code Constraint → Body A val 𝒞 Code Constraint
  constr : (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)  
            → Body A val 𝒞 Code Constraint → Body A val 𝒞 Code Constraint

-- Flatten a Body into a plain List of Literals
toLiteralList : ∀ {Atom val 𝒞 Code Constraint} → Body Atom val 𝒞 Code Constraint → List (Literal Atom 𝒞 Code Constraint)
toLiteralList (end a _) = atom a ∷ []
toLiteralList (endst c) = constraint c ∷ []
toLiteralList (cons a _ xs) = atom a ∷ toLiteralList xs
toLiteralList (constr c xs) = constraint c ∷ toLiteralList xs

pattern _•ₐ x = end x _
pattern _∧ₐ_ x y = cons x _ y
pattern _↣_• code x = endst (inj₁ (code :-: x))
pattern _↪_• code x = endst (inj₂ (code :-: x))
pattern _↣_∧_ code x y = constr (inj₁ (code :-: x)) y
pattern _↪_∧_ code x y = constr (inj₂ (code :-: x)) y

-- A compiled clause: head atom with a flat literal body
record ClauseI
  (Atom : Set) 
  (𝒞 : Set) 
  (Code : (𝒞 → Set))
  (Constraint : (𝒞 → Set)) : Set where
  constructor _:--_
  field
    head : Atom
    body : List (Literal Atom 𝒞 Code Constraint)
    ⦃ inst ⦄ : FTUtils Atom
    ⦃ instAt ⦄ : AtomUtils Atom 𝒞 Code Constraint

-- Surface syntax for rules: facts, rules with bodies, sequencing, and variable binding
data Clause 
  (A : Set) 
  (val : Where → A → Set)
  (𝒞 : Set) 
  (Code : (𝒞 → Set))
  (Constraint : (𝒞 → Set)) : Set₁ where
  fact : ⦃ FTUtils A ⦄ → ⦃ AtomUtils A 𝒞 Code Constraint ⦄ → (atom : A)
       → val headOfRule atom
       → Clause A val 𝒞 Code Constraint

  rule : ⦃ FTUtils A ⦄ → ⦃ AtomUtils A 𝒞 Code Constraint ⦄ → (atom : A)
       → val headOfRule atom
       → Body A (val bodyOfRule) 𝒞 Code Constraint
       → Clause A val 𝒞 Code Constraint

  _>>_ : Clause A val 𝒞 Code Constraint → Clause A val 𝒞 Code Constraint → Clause A val 𝒞 Code Constraint

  _>>=_ : {B : Set} → ⦃ MakeVar B ⦄ → B → (B → Clause A val 𝒞 Code Constraint) → Clause A val 𝒞 Code Constraint

-- Compile surface Clause syntax to a list of ClauseI
toIntern : ∀ {Atom val 𝒞 Code Constraint} → Clause Atom val 𝒞 Code Constraint → List (ClauseI Atom 𝒞 Code Constraint)
toIntern (fact a _) = a :-- [] ∷ []
toIntern (rule a _ xs) = a :-- toLiteralList xs ∷ []
toIntern (cl0 >> cl1) = toIntern cl0 ++ toIntern cl1
toIntern _ = []

pattern _• x = fact x _
pattern _:-_ x y = rule x _ y

infix 60 _•
infix 60 _•ₐ
infix 60 _↪_•
infix 60 _↣_•
infixr 50 _∧ₐ_
infixr 50 _↪_∧_
infixr 50 _↣_∧_

infix 30 _:-_

-- Resolve >>= binders into fresh variable ids, threading a counter
applyVars
  : ∀ {A val 𝒞 Code Constraint}
  → Clause A val 𝒞 Code Constraint
  → ℕ → ℕ × Clause A val 𝒞 Code Constraint
applyVars (fact f p)     c = c , fact f p
applyVars (rule f p b)   c = c , rule f p b
applyVars (c₁ >> c₂)     c =
  let (c₁' , r₁) = applyVars c₁ c
      (c₂' , r₂) = applyVars c₂ c₁'
  in  c₂' , (r₁ >> r₂)

applyVars (_>>=_ {B} x k) c =
  let a      = fresh c
      c'     = suc c
      result = k a
      (c'' , r) = applyVars result c'
  in c'' , r

-- Interface for a constraint solver for one solver domain c
record Solver (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set₁ where
  field
    solve : 
     {A : Set}
     → (c : 𝒞)
     → ⦃ DecEq 𝒞 ⦄
     → ⦃ FTUtils (Code c) ⦄
     → ⦃ ValueUtils 𝒞 Code Constraint ⦄
     → ⦃ FTUtils (Constraint c) ⦄ 
     → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
     → (occurs : ℕ → A → Bool)
     → (apply : ℕ → Code c → A → A)
     → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
     → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
     → A
     → List (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) × A)
open Solver ⦃...⦄ public

-- Interface for grounding (extracting variable bindings from constraints)
record Grounder (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set₁ where
  field
    ground : 
     {A : Set}
     → (c : 𝒞)
     → ⦃ DecEq 𝒞 ⦄
     → ⦃ FTUtils (Code c) ⦄
     → ⦃ ValueUtils 𝒞 Code Constraint ⦄
     → ⦃ FTUtils (Constraint c) ⦄ 
     → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
     → (occurs : ℕ → A → Bool)
     → (apply : ℕ → Code c → A → A)
     → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
     → A
     → List ((ℕ × Code c) ⊎ (ℕ × Code c)) × A
open Grounder ⦃...⦄ public

-- Interface for scheduling constraint propagation across solvers
record Scheduler (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set₁ where
  field
    schedule :
     ⦃ DecEq 𝒞 ⦄
     → ⦃ ValueUtils 𝒞 Code Constraint ⦄
     → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
     → ⦃ Solver 𝒞 Code Constraint ⦄
     → List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
     → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
     → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
open Scheduler ⦃...⦄ public

-- Output of the solver: a list of variable-to-Σᵢ bindings
Subst : (𝒞 : Set) → (Code : (𝒞 → Set)) → (Constraint : (𝒞 → Set)) → Set
Subst C code cns = List (ℕ × (Σᵢ C code code cns))

-- Universe of syntactic categories that carry variables
data HasVariables : Set where
  domainConstraint   : HasVariables
  genericConstraint  : HasVariables
  mixedConstraint    : HasVariables
  atom               : HasVariables
  literal            : HasVariables
  clause             : HasVariables
  listOf             : HasVariables → HasVariables
  domainExpr         : HasVariables

-- Decode a HasVariables tag to its corresponding Agda type
⟦_,_,_,_,_⟧ᵥ :
  (𝒞 : Set)
  → (Code : (𝒞 → Set))
  → (Constraint : (𝒞 → Set))
  → Set
  → HasVariables
  → Set
⟦ C , code , cns , at , domainConstraint ⟧ᵥ = Σᵢ C (Dual ∘ cns) code cns
⟦ C , code , cns , at , genericConstraint ⟧ᵥ = Σᵢ C (ℒ ∘ code) code cns
⟦ C , code , cns , at , mixedConstraint ⟧ᵥ = (Σᵢ C (ℒ ∘ code) code cns) ⊎ (Σᵢ C (Dual ∘ cns) code cns)
⟦ _ , code , cns , at , atom ⟧ᵥ = at ×ᵢ at
⟦ C , code , cns , at , literal ⟧ᵥ   = Literal at C code cns
⟦ C , code , cns , at , clause ⟧ᵥ    = ClauseI at C code cns
⟦ C , code , cns , at , listOf h ⟧ᵥ    = List (⟦ C , code , cns , at , h ⟧ᵥ)
⟦ C , code , cns , at , domainExpr ⟧ᵥ  = Σᵢ C code code cns