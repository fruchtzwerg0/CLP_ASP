module Term.clp where

open import Term.types
open import Term.ftUtilsDerivation
open import Term.utilities
open import Views.find
open import Views.findall
open import Data.Bool
open import Data.String 
  using (String; _==_)
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.List 
  using (List; []; _∷_; _++_; map; length; zip; zipWith; concat; foldr)
open import Data.Maybe 
  using (Maybe; just; nothing; map; is-just)
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)
open import Function.Base

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.PropositionalEquality

open import Generics

maybeToList : {A : Set} → Maybe (List A) → List A
maybeToList nothing  = []
maybeToList (just x) = x

-- TO DO: use Maybe.map to erase second pattern match
bindAndRename : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → Atom 
  → ℕ 
  → ClauseI Atom 𝒞 Code Constraint 
  → List (Literal Atom 𝒞 Code Constraint)
bindAndRename {Atom}{C}{Code}{Constraint} ⦃ ft ⦄ atom₀ n (atom₁ :-- l)  =
  ((Data.List.map (constraint ∘ inj₁)) ∘ maybeToList ∘ (zipMatch ft atom₀)) (increment ft (suc n) atom₁) 
   ++ Data.List.map (incrementLiteral (suc n)) l

equalFunctor : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ FTUtils Atom ⦄
  → Atom
  → ClauseI Atom 𝒞 Code Constraint
  → Bool
equalFunctor ⦃ ft ⦄ l r = functor ⦃ ft ⦄ l == (functor ⦃ ft ⦄ ∘ ClauseI.head) r

EvalType : Set → (𝒞 : Set) → (𝒞 → Set) → (𝒞 → Set) → Set → Set
EvalType Atom 𝒞 Code Constraint Custom = 
  Custom
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (Literal Atom 𝒞 Code Constraint)
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))

-- Generic evaluation function, terminating required because this requires Turing-completeness
eval : 
  ∀ {Atom 𝒞 Code Constraint}
  → {Custom : Set}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  --→ ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (intercept : 
    ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils Atom ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
    → ⦃ Solver 𝒞 Code Constraint ⦄
    --→ ⦃ Grounder 𝒞 Code Constraint ⦄
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → EvalType Atom 𝒞 Code Constraint Custom)
  → EvalType Atom 𝒞 Code Constraint Custom

-- base case
eval _ custom program [] right = (custom , right) ∷ []

-- cases for splitting an atom into the body of its unified clause
eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ _ _ program (atom at ∷ left) right with findAll (is-just ∘ zipMatch ato at ∘ ClauseI.head) program

eval {Atom}{C}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ intercept custom .(forget split) (atom at ∷ left) right | matches split _ _
  with Data.List.map (λ {cl → 
    intercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄
          custom 
          (forget split)
          ((bindAndRename ⦃ ato ⦄ at (((foldr _⊔_ 0 ∘ collectVarsᵥ C Code Constraint) (atom ⦃ ft ⦄ ⦃ ato ⦄ at ∷ left)) ⊔ ((foldr _⊔_ 0 ∘ collectVarsᵥ {_}{Atom} C Code Constraint) right)) cl) ++ left)
          right})
      (first split)
eval _ _ .(forget split) (atom at ∷ left) right | matches split _ _
  | derivations with findAll (λ { (_ ∷ _) → true ; [] → false}) derivations
eval _ _ .(forget split) (atom at ∷ left) right | matches split _ _
  | .(forget splitNondet) | matches splitNondet _ _ = (concat ∘ first) splitNondet

eval intercept custom program (constraint cnstr ∷ left) right with (schedule ∘ Data.List.map (_∷_ cnstr)) right
eval intercept custom program (constraint cnstr ∷ left) right | newConstraints = intercept  custom program left newConstraints
{-
clpExecute : 
  ∀ {ConcreteAtom AbstractAtom 𝒞 validate Code Constraint Custom}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils AbstractAtom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils AbstractAtom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  --→ ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (convertProgram : List (ClauseI ConcreteAtom 𝒞 Code Constraint) → List (ClauseI AbstractAtom 𝒞 Code Constraint))
  → (convertQuestion : List (Literal ConcreteAtom 𝒞 Code Constraint) → List (Literal AbstractAtom 𝒞 Code Constraint))
  → (intercept : 
    ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils AbstractAtom ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ AtomUtils AbstractAtom 𝒞 Code Constraint ⦄
    → ⦃ Solver 𝒞 Code Constraint ⦄
    --→ ⦃ Grounder 𝒞 Code Constraint ⦄
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → List ((AbstractAtom → Bool) × 
    EvalType AbstractAtom 𝒞 Code Constraint Custom)
    → EvalType AbstractAtom 𝒞 Code Constraint Custom)
  → ( : 
    List ((AbstractAtom → Bool) × 
    EvalType AbstractAtom 𝒞 Code Constraint Custom))
  → Custom
  → Clause ConcreteAtom validate 𝒞 Code Constraint
  → Body ConcreteAtom (validate bodyOfRule) 𝒞 Code Constraint
  --→ List (Custom × (List ∘ List) ((Σᵢ 𝒞 (_×_ ℕ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → Code c × (List ∘ Code) c) Code Constraint)))
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
clpExecute convertProgram convertQuestion intercept  custom program question = 
  let result = eval intercept  custom ((convertProgram ∘ toIntern ∘ proj₂ ∘ applyVars program) 0) ((convertQuestion ∘ toLiteralList) question) [] in
  Data.List.map (λ (_ , l) → Data.List.map (λ (_:-:_ c _ ⦃ instCode ⦄ ⦃ instCns ⦄) → ground c) l) result
-}

clpExecute : 
  ∀ {ConcreteAtom AbstractAtom 𝒞 Code Constraint Custom}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils AbstractAtom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils AbstractAtom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  --→ ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (convertProgram : List (ClauseI ConcreteAtom 𝒞 Code Constraint) → List (ClauseI AbstractAtom 𝒞 Code Constraint))
  → (convertQuestion : List (Literal ConcreteAtom 𝒞 Code Constraint) → List (Literal AbstractAtom 𝒞 Code Constraint))
  → (intercept : 
    ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils AbstractAtom ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ AtomUtils AbstractAtom 𝒞 Code Constraint ⦄
    → ⦃ Solver 𝒞 Code Constraint ⦄
    --→ ⦃ Grounder 𝒞 Code Constraint ⦄
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → EvalType AbstractAtom 𝒞 Code Constraint Custom)
  → Custom
  → List (ClauseI ConcreteAtom 𝒞 Code Constraint)
  → List (Literal ConcreteAtom 𝒞 Code Constraint)
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))
clpExecute ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ convertProgram convertQuestion intercept custom program question = 
  eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ 
    (intercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄)
    custom 
    (convertProgram program) 
    (convertQuestion question) 
    []