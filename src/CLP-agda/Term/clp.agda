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

-- Generic evaluation function, terminating required because this requires Turing-completeness
{-# TERMINATING #-}
eval : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (Literal Atom 𝒞 Code Constraint)
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → (findAll : Bool)
  → if findAll 
    then (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
    else (Maybe ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) -- type depends on whether findall mode is activated

-- base cases for the two modi
eval program [] right true = right ∷ []
eval program [] right false = just right

-- cases for splitting an atom into the body of its unified clause
eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ program (atom at ∷ left) right _ with findAll (is-just ∘ zipMatch ato at ∘ ClauseI.head) program
eval {Atom}{C}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ .(forget split) (atom at ∷ left) right false | matches split _ _ 
  with Data.List.map (λ {cl → 
    eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (forget split)
          ((bindAndRename ⦃ ato ⦄ at (((foldr _⊔_ 0 ∘ collectVarsᵥ C Code Constraint) (atom at ⦃ ft ⦄ ⦃ ato ⦄ ∷ left)) ⊔ ((foldr _⊔_ 0 ∘ collectVarsᵥ {_}{Atom} C Code Constraint) right)) cl) ++ left)
          right
          false})
      (first split)

eval {c} .(forget split) (atom at ∷ left) right false | matches split _ _
  | derivations with find (λ {(just _) → true ; nothing → false}) derivations
eval .(forget split) (atom at ∷ left) right _ | matches split _ _
  | .(_ ++ successful-derivation ∷ _) | found before successful-derivation _ after = successful-derivation
eval .(forget split)        (atom at ∷ left) right _ | matches split _ _
  | no-successful-derivations         | not-found _ = nothing

eval {Atom}{C}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ .(forget split) (atom at ∷ left) right true | matches split _ _
  with Data.List.map (λ {cl → 
    eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄
          (forget split)
          ((bindAndRename ⦃ ato ⦄ at (((foldr _⊔_ 0 ∘ collectVarsᵥ C Code Constraint) (atom at ⦃ ft ⦄ ⦃ ato ⦄ ∷ left)) ⊔ ((foldr _⊔_ 0 ∘ collectVarsᵥ {_}{Atom} C Code Constraint) right)) cl) ++ left)
          right
          true})
      (first split)
eval {c} .(forget split) (atom at ∷ left) right true | matches split _ _
  | derivations with findAll (λ {(_ ∷ _) → true ; [] → false}) derivations
eval .(forget split) (atom at ∷ left) right _ | matches split _ _
  | .(forget splitNondet) | matches splitNondet _ _ = concat (first splitNondet)

-- cases for addition of domain constraints to the right side for preliminary consistency check by solver
eval program (constraint cnstr ∷ left) right false with schedule (cnstr ∷ right)
eval program (constraint cnstr ∷ left) right false | just newRight = eval program left newRight false
eval program (constraint cnstr ∷ left) right false | nothing = nothing

eval program (constraint cnstr ∷ left) right true with schedule (cnstr ∷ right)
eval program (constraint cnstr ∷ left) right true | just newRight = eval program left newRight true
eval program (constraint cnstr ∷ left) right true | nothing = []

clpExecute : 
  ∀ {ConcreteAtom AbstractAtom 𝒞 validate Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils AbstractAtom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils AbstractAtom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (convertProgram : List (ClauseI ConcreteAtom 𝒞 Code Constraint) → List (ClauseI AbstractAtom 𝒞 Code Constraint))
  → (convertQuestion : List (Literal ConcreteAtom 𝒞 Code Constraint) → List (Literal AbstractAtom 𝒞 Code Constraint))
  → (metaPredicates : List (
    (AbstractAtom → Bool) × 
    ((zipAtom : AbstractAtom → AbstractAtom → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
    → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
    → Clause ConcreteAtom validate 𝒞 Code Constraint
    → Body ConcreteAtom (validate bodyOfRule) 𝒞 Code Constraint
    → (findAll : Bool)
    → if findAll 
      then (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
      else (Maybe ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))))
  → Clause ConcreteAtom validate 𝒞 Code Constraint
  → Body ConcreteAtom (validate bodyOfRule) 𝒞 Code Constraint
  → (findAll : Bool)
  → if findAll 
    then (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
    else (Maybe ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) -- type depends on whether findall mode is activated
clpExecute convertProgram convertQuestion metaPredicates program question = 
  eval ((convertProgram ∘ toIntern ∘ proj₂ ∘ applyVars program) 0) ((convertQuestion ∘ toLiteralList) question) []