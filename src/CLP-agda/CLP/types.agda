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


data ℒ (A : Set) : Set where
  _=ℒ_ : A → A → ℒ A
  _≠ℒ_ : A → A → ℒ A

infixr 80 _=ℒ_
infixr 80 _≠ℒ_

data Dual (A : Set) : Set where
  default : A → Dual A
  dual : A → Dual A

-- ---------------------------------------------------------------------

record MakeVar {l} (A : Set l) : Set l where
  field
    fresh : ℕ → A
    new : A
open MakeVar ⦃...⦄ public

data Where : Set where
  headOfRule : Where
  bodyOfRule : Where

record Σᵢ (A : Set) (B : A → Set) (Code : A → Set) (Cns : A → Set) : Set

record ConstraintUtils (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    zipMatch : (c : 𝒞) → Constraint c → Constraint c → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
    increment : (c : 𝒞) → ℕ → Constraint c → Constraint c
    apply : (c₀ : 𝒞) → (c₁ : 𝒞) → ℕ → Code c₀ → Constraint c₁ → Constraint c₁
open ConstraintUtils ⦃...⦄ public

record ValueUtils (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    zipMatch : (c : 𝒞) → Code c → Code c → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
    increment : (c : 𝒞) → ℕ → Code c → Code c
    apply : (c₀ : 𝒞) → (c₁ : 𝒞) → ℕ → Code c₀ → Code c₁ → Code c₁
open ValueUtils ⦃...⦄ public

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

record AtomUtils (Atom : Set) (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    zipMatch : Atom → Atom → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
    increment : ℕ → Atom → Atom
open AtomUtils ⦃...⦄ public

record _×ᵢ_ (A : Set) (B : Set) : Set where
  constructor _<ᵢ
  field
    code    : A
    ⦃ inst ⦄ : FTUtils B
open _×ᵢ_ public

data Literal 
  (A : Set)
  (𝒞 : Set) 
  (Code : (𝒞 → Set))
  (Constraint : (𝒞 → Set)) : Set where
  atom : ⦃ FTUtils A ⦄ → ⦃ AtomUtils A 𝒞 Code Constraint ⦄ → A → Literal A 𝒞 Code Constraint
  constraint : (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) → Literal A 𝒞 Code Constraint

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
     → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c) × A
     → List (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint) × A)
open Solver ⦃...⦄ public

record Grounder (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set where
  field
    ground : (c : 𝒞)
     → ⦃ DecEq 𝒞 ⦄
     → ⦃ FTUtils (Code c) ⦄
     → ⦃ ValueUtils 𝒞 Code Constraint ⦄
     → ⦃ FTUtils (Constraint c) ⦄ 
     → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
     → List ((ℒ ∘ Code) c ⊎ (Dual ∘ Constraint) c)
     → List ((ℕ × Code c) ⊎ (ℕ × Code c))
open Grounder ⦃...⦄ public

record Scheduler (𝒞 : Set) (Code : (𝒞 → Set)) (Constraint : (𝒞 → Set)) : Set₁ where
  field
    schedule :
     ⦃ DecEq 𝒞 ⦄
     → ⦃ ValueUtils 𝒞 Code Constraint ⦄
     → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
     → ⦃ Solver 𝒞 Code Constraint ⦄
     → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
     → (List ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint ⊎ Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)
open Scheduler ⦃...⦄ public

-- Generic type for Substitutions (Output of the solver).
Subst : (𝒞 : Set) → (Code : (𝒞 → Set)) → (Constraint : (𝒞 → Set)) → Set
Subst C code cns = List (ℕ × (Σᵢ C code code cns))

-- Generic universe codes for entities that have variables.
-- Extensively used by the utilities.
data HasVariables : Set where
  domainConstraint   : HasVariables
  genericConstraint   : HasVariables
  mixedConstraint   : HasVariables
  atom        : HasVariables
  literal     : HasVariables
  clause      : HasVariables
  listOf      : HasVariables → HasVariables
  domainExpr  : HasVariables

-- Decoding function for HasVariables
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