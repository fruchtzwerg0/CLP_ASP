module CLP.clp where

open import CLP.types
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import Data.Bool hiding (_≟_)
open import Data.String 
  using (String; _==_)
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.List hiding (takeWhile; dropWhile)
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

open import CLP.outputFormatter

maybeToList : {A : Set} → Maybe (List A) → List A
maybeToList nothing  = []
maybeToList (just x) = x


bindAndRename : 
  {Atom : Set}
  → {𝒞 : Set}
  → {Code : (𝒞 → Set)}
  → {Constraint : (𝒞 → Set)}
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
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

takeWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
takeWhile p []       = []
takeWhile p (x ∷ xs) with p x
... | true  = x ∷ takeWhile p xs
... | false = []

dropWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
dropWhile p []       = []
dropWhile p (x ∷ xs) with p x
... | true  = dropWhile p xs
... | false = x ∷ xs

EvalType : Set → (𝒞 : Set) → (𝒞 → Set) → (𝒞 → Set) → Set → Set
EvalType Atom 𝒞 Code Constraint Custom = 
  Custom
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (Literal Atom 𝒞 Code Constraint)
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List (Custom × (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)))

-- Generic evaluation function (implements operational semantics of SLD-resolution)
eval : 
  ∀ {Atom 𝒞 Code Constraint}
  → {Custom : Set}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (intercept : 
    ⦃ DecEq 𝒞 ⦄
    → ⦃ FTUtils Atom ⦄
    → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
    → ⦃ ValueUtils 𝒞 Code Constraint ⦄
    → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
    → ⦃ Solver 𝒞 Code Constraint ⦄
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → EvalType Atom 𝒞 Code Constraint Custom)
  → EvalType Atom 𝒞 Code Constraint Custom

-- base case
eval _ custom program [] right = (custom , right) ∷ []

-- cases for splitting an atom into the body of its unified clause
eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ _ _ program (atom at ∷ left) right with filterᵇ (is-just ∘ zipMatch ato at ∘ ClauseI.head) program

eval {Atom}{C}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ intercept custom program (atom at ∷ left) right | split =
  (concat ∘ Data.List.map (λ cl → 
    intercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄
          custom 
          program
          ((bindAndRename ⦃ ato ⦄ at (((foldr _⊔_ 0 ∘ collectVarsᵥ C Code Constraint) (atom ⦃ ft ⦄ ⦃ ato ⦄ at ∷ left)) ⊔ ((foldr _⊔_ 0 ∘ collectVarsᵥ {_}{Atom} C Code Constraint) right)) cl) ++ left)
          right))
      split

eval intercept custom program (constraint cnstr ∷ left) right with 
  (schedule ∘ Data.List.map (λ x → (_++_ x ∘ catMaybes ∘ takeWhile is-just ∘ Data.List.map (λ { (constraint x) → just x ; (atom _) → nothing })) (constraint cnstr ∷ left))) right
eval intercept custom program (constraint cnstr ∷ left) right | [] = []
eval intercept custom program (constraint cnstr ∷ left) right | newConstraints = 
  intercept custom program (dropWhile (λ { (constraint _) → true ; (atom _) → false }) left) newConstraints

{-# TERMINATING #-}
defaultIntercept :
  ∀ {Atom 𝒞 Code Constraint Custom}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → EvalType Atom 𝒞 Code Constraint Custom
defaultIntercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ = 
  eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (defaultIntercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄)

{-# TERMINATING #-}
groundSchedule :
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → List 𝒞
  → List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
groundSchedule c acc [] = acc
groundSchedule {C}{Code}{Constraint} ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ val ⦄ c acc ((inj₁ (c₀ :-: x)) ∷ xs) = 
  let (gr , (newOtherGround , newOther)) = ground 
              c₀ 
              (λ n (grou , nonGrou) → 
                occursᵥ {listOf mixedConstraint} {⊤} C Code Constraint n nonGrou ∨
                any (λ {(inj₁ (c :-: (_ , a))) → occurs n a ; (inj₂ (c :-: (_ , a))) → occurs n a } ) grou)
              (λ n sub (grou , nonGrou) → 
                Data.List.map (λ {(inj₁ (c :-: (m , a))) → (inj₁ (c :-: (m , apply val c₀ c n sub a))) ; 
                                  (inj₂ (c :-: (m , a))) → (inj₂ (c :-: (m , apply val c₀ c n sub a))) } ) grou ,
                Data.List.map (applyMixedConstraint c₀ n sub) nonGrou) 
              ((inj₁ x ∷ (catMaybes ∘ Data.List.map (getPermission c₀)) xs) , (acc , (catMaybes ∘ Data.List.map (getElse c₀)) xs)) in
  groundSchedule (c₀ ∷ c) (newOtherGround ++ Data.List.map (generalizeGround c₀) gr) newOther
groundSchedule {C}{Code}{Constraint} ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ val ⦄ c acc ((inj₂ (c₀ :-: x)) ∷ xs) = 
  let (gr , (newOtherGround , newOther)) = ground 
              c₀ 
              (λ n (grou , nonGrou) → 
                occursᵥ {listOf mixedConstraint} {⊤} C Code Constraint n nonGrou ∨
                any (λ {(inj₁ (c :-: (_ , a))) → occurs n a ; (inj₂ (c :-: (_ , a))) → occurs n a } ) grou)
              (λ n sub (grou , nonGrou) → 
                Data.List.map (λ {(inj₁ (c :-: (m , a))) → (inj₁ (c :-: (m , apply val c₀ c n sub a))) ; 
                                  (inj₂ (c :-: (m , a))) → (inj₂ (c :-: (m , apply val c₀ c n sub a))) } ) grou ,
                Data.List.map (applyMixedConstraint c₀ n sub) nonGrou) 
              ((inj₂ x ∷ (catMaybes ∘ Data.List.map (getPermission c₀)) xs) , (acc , (catMaybes ∘ Data.List.map (getElse c₀)) xs)) in
  groundSchedule (c₀ ∷ c) (newOtherGround ++ Data.List.map (generalizeGround c₀) gr) newOther

-- Entry point for clp executions. Can be parameterized with conversion from CST to AST with convertProgram (for the program) and convertQuestion (for the question)
-- An intercepter can be passed, in which the SLD-resolution can be adapted (for example co-SLD), and meta predicates can be executed.
-- Custom is a custom state that can be passed (also through the intercepter), and that can be used for custom outputs with custom additional information
-- (stack trace, CHS, etc.)
clpExecute : 
  ∀ {ConcreteAtom AbstractAtom 𝒞 Code Constraint Custom}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils AbstractAtom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils AbstractAtom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Grounder 𝒞 Code Constraint ⦄
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
    → ⦃ Scheduler 𝒞 Code Constraint ⦄
    → EvalType AbstractAtom 𝒞 Code Constraint Custom)
  → (shouldGround : Bool)
  → Custom
  → List (ClauseI ConcreteAtom 𝒞 Code Constraint)
  → List (Literal ConcreteAtom 𝒞 Code Constraint)
  → List (Custom × 
    List (if shouldGround 
    then List ((Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint) ⊎ (Σᵢ 𝒞 (λ c → ℕ × Code c) Code Constraint))
    else List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))))
clpExecute ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄ convertProgram convertQuestion intercept true custom program question = 
  let result = intercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄
                custom 
                (convertProgram program) 
                (convertQuestion question)
                ([] ∷ []) in
  let cust = Data.List.map proj₁ result in
  let payl = Data.List.map proj₂ result in
    Data.List.zip cust (
      Data.List.map (
        Data.List.map (groundSchedule [] [])) payl)
clpExecute ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄ convertProgram convertQuestion intercept false custom program question = 
  intercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄
                custom 
                (convertProgram program) 
                (convertQuestion question)
                ([] ∷ [])

top : ⊤
top = record {}

defaultExecute : 
  ∀ {Atom validate 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Grounder 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (shouldGround : Bool)
  → Clause Atom validate 𝒞 Code Constraint
  → Body Atom (validate bodyOfRule) 𝒞 Code Constraint
  → (List ∘ List) String
defaultExecute {_}{_}{C}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄ shouldGround program question = 
  (Data.List.map (Data.List.map (formatOutput shouldGround (collectVarsᵥ C Code Constraint (toLiteralList question))) ∘ proj₂) ∘ clpExecute ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ grou ⦄ ⦃ sched ⦄
      id 
      id 
      (defaultIntercept ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄)
      shouldGround
      top
      ((toIntern ∘ proj₂ ∘ applyVars program) 0)) (toLiteralList question)