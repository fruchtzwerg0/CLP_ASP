module ASP.loops where

open import CLP.types hiding (_>>=_)
open import CLP.ftUtilsDerivation
open import CLP.utilities
open import ASP.types
open import Data.Bool hiding (_≟_)
open import Data.List
open import Data.String hiding (_≟_; concat; show; replicate; length)
open import Data.Nat hiding (equal; _≟_)
open import Data.Nat.Show
open import Data.List.Base
open import Data.List.Membership.DecSetoid using (_∈?_)
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

open import CLP.clp
open import CLP.outputFormatter

open import ASP.dual
open import ASP.cforall

-- FTUtils needs to be implemented also for ASPAtom

occursExi : 
  ∀ {𝒞 Code Constraint}
  → ℕ 
  → Σᵢ 𝒞 Code Code Constraint 
  → Bool
occursExi n (_:-:_ c x) = occurs n x

collectVarsExi : 
  ∀ {𝒞 Code Constraint}
  → Σᵢ 𝒞 Code Code Constraint 
  → List ℕ
collectVarsExi (_:-:_ c x) = collectVars x

instance aspFT : ∀ {Atom 𝒞 Code Constraint} → ⦃ FTUtils Atom ⦄ → FTUtils (ASPAtom Atom 𝒞 Code Constraint)
         aspFT .functor (wrap at _ _) = functor at
         aspFT .functor (forAll _ _) = "forAll"
         aspFT .functor nmrCheck = "nmrCheck"
         aspFT .functor (chk _ _ _) = "chk"
         aspFT .getNat _ = nothing
         aspFT .varName _ = nothing
         aspFT {At}{C}{Code}{Constraint} ⦃ ft ⦄ .occurs n (wrap at _ x) = occurs n at ∨ any (occursExi n) x
         aspFT {At}{C}{Code}{Constraint} ⦃ ft ⦄ .occurs n (forAll x y) = occursExi n x ∨ occurs n y
         aspFT .occurs n nmrCheck = false
         aspFT {At}{C}{Code}{Constraint} ⦃ ft ⦄ .occurs n (chk _ _ x) = any (occursExi n) x
         aspFT {At}{C}{Code}{Constraint} ⦃ ft ⦄ .collectVars (wrap at _ x) = collectVars at Data.List.++ (concat ∘ Data.List.map collectVarsExi) x
         aspFT {At}{C}{Code}{Constraint} ⦃ ft ⦄ .collectVars (forAll x y) = collectVarsExi x Data.List.++ collectVars y
         aspFT .collectVars nmrCheck = []
         aspFT {At}{C}{Code}{Constraint} ⦃ ft ⦄ .collectVars (chk _ _ x) = (concat ∘ Data.List.map collectVarsExi) x

incrementExi : 
  ∀ {𝒞 Code Constraint}
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄ 
  → ℕ 
  → Σᵢ 𝒞 Code Code Constraint 
  → Σᵢ 𝒞 Code Code Constraint
incrementExi ⦃ val ⦄ n (_:-:_ c x) = (_:-:_ c (increment val c n x))

applyExi : 
  ∀ {𝒞 Code Constraint}
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄ 
  → (c : 𝒞)
  → ℕ 
  → Code c
  → Σᵢ 𝒞 Code Code Constraint 
  → Σᵢ 𝒞 Code Code Constraint
applyExi ⦃ val ⦄ c₀ n y (_:-:_ c x) = (_:-:_ c (apply val c₀ c n y x))

zipMatchExi : 
  ∀ {𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄ 
  → List (Σᵢ 𝒞 Code Code Constraint) 
  → List (Σᵢ 𝒞 Code Code Constraint) 
  → (Maybe ∘ List) (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)
zipMatchExi (x ∷ xs) [] = nothing
zipMatchExi [] (x ∷ xs) = nothing
zipMatchExi [] [] = just []
zipMatchExi ((_:-:_ c₀ x ⦃ ft ⦄ ⦃ val ⦄ ⦃ dec ⦄ ⦃ va ⦄ ⦃ sho ⦄ ⦃ shoj ⦄) ∷ xs) ((_:-:_ c₁ y ⦃ _ ⦄ ⦃ _ ⦄) ∷ ys) with c₀ ≟ c₁
... | yes refl = zipMatchExi xs ys Data.Maybe.>>= (just ∘ _∷_ (_:-:_ c₀ (x =ℒ y) ⦃ ft ⦄ ⦃ val ⦄ ⦃ dec ⦄ ⦃ va ⦄ ⦃ sho ⦄ ⦃ shoj ⦄))
... | no _ = nothing

-- AtomUtils needs to be implemented for ASPAtom

instance aspAtom : ∀ {Atom 𝒞 Code Constraint} 
                   → ⦃ DecEq 𝒞 ⦄
                   → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄ 
                   → ⦃ ValueUtils 𝒞 Code Constraint ⦄ 
                   → AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
         aspAtom {_}{C}{Code}{Constraint} ⦃ _ ⦄ ⦃ at ⦄ .zipMatch (wrap at₀ n₀ x₀) (wrap at₁ n₁ x₁) = 
          if (n₀ ≡ᵇ n₁) ∧ (is-just ∘ zipMatch at at₀) at₁
          then zipMatchExi x₀ x₁
          else nothing
         aspAtom {_}{C}{Code}{Constraint} .zipMatch (forAll x₀ y₀) (forAll x₁ y₁) = 
          zipMatch aspAtom y₀ y₁ Data.Maybe.>>= (λ y → zipMatchExi (x₀ ∷ []) (x₁ ∷ []) Data.Maybe.>>= (λ z → just (y Data.List.++ z)))
         aspAtom .zipMatch nmrCheck nmrCheck = just []
         aspAtom {_}{C}{Code}{Constraint} ⦃ at ⦄ .zipMatch (chk a₀ b₀ x₀) (chk a₁ b₁ x₁) = 
          if (a₀ ≡ᵇ a₁) Data.Bool.∧ (b₀ ≡ᵇ b₁)
          then zipMatchExi x₀ x₁
          else nothing
         aspAtom .zipMatch _ _ = nothing
         aspAtom ⦃ _ ⦄ ⦃ att ⦄ .increment n (wrap at y x) = wrap (increment att n at) y (Data.List.map (incrementExi n) x)
         aspAtom .increment n (forAll x y) = forAll (incrementExi n x) (increment aspAtom n y)
         aspAtom .increment n nmrCheck = nmrCheck
         aspAtom .increment n (chk a b x) = chk a b (Data.List.map (incrementExi n) x)
         aspAtom ⦃ _ ⦄ ⦃ att ⦄ .apply c n z (wrap at y x) = wrap (apply att c n z at) y (Data.List.map (applyExi c n z) x)
         aspAtom .apply c n z (forAll x y) = forAll (applyExi c n z x) (apply aspAtom c n z y)
         aspAtom .apply c n z nmrCheck = nmrCheck
         aspAtom .apply c n z (chk a b x) = chk a b (Data.List.map (applyExi c n z) x)

-- ASPUtils needs to be implemented for ASPAtom

instance  aspAtomUtils : ∀ {Atom 𝒞 Code Constraint} → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄ → ASPUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint
          aspAtomUtils .ASP.types.not (wrap at a b) = wrap (ASP.types.not at) a b
          aspAtomUtils .ASP.types.not (forAll a b) = forAll a (ASP.types.not b)
          aspAtomUtils .ASP.types.not nmrCheck = nmrCheck
          aspAtomUtils .ASP.types.not (chk a b c) = chk a b c
          aspAtomUtils .isNot (wrap at _ _) = isNot at
          aspAtomUtils .isNot (forAll a b) = isNot b
          aspAtomUtils .isNot nmrCheck = false
          aspAtomUtils .isNot (chk a b c) = true
          aspAtomUtils .ASP.types.isFalse _ = false
          aspAtomUtils .toggle (wrap at a b) = wrap (toggle at) a b
          aspAtomUtils .toggle (forAll a b) = forAll a (toggle b)
          aspAtomUtils .toggle nmrCheck = nmrCheck
          aspAtomUtils .toggle (chk a b c) = chk a b c

instance  aspShow : ∀ {Atom 𝒞 Code Constraint} → ⦃ Show Atom ⦄ → Show (ASPAtom Atom 𝒞 Code Constraint)
          aspShow .Generics.show (wrap at a b) = Generics.show at Data.String.++ " " Data.String.++ Data.Nat.Show.show a
          aspShow .Generics.show (forAll a b) = "forAll "
          aspShow .Generics.show nmrCheck = "nmrCheck"
          aspShow .Generics.show (chk a b c) = "chk " Data.String.++ Data.Nat.Show.show a Data.String.++ " " Data.String.++ Data.Nat.Show.show b

{-# TERMINATING #-}
mod : ℕ → ℕ → ℕ
mod n zero = n
mod n m with compare n m
... | less _ _ = n
... | _ = mod (n ∸ m) m

-- Checks the CHS for already proven atoms.

checkCHS :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils Atom ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List Atom
  → Atom
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) ⊎ ⊤
checkCHS {Atom}{C}{Code}{Constraint} ⦃ dec ⦄ ⦃ ft ⦄ ⦃ at ⦄ constraints x y with 
  (any (Data.Bool.not ∘ null) 
  ∘ Data.List.map (λ unif → schedule (Data.List.map inj₁ unif) constraints) 
  ∘ catMaybes 
  ∘ Data.List.map (zipMatch at (toggle y))) x
... | true = inj₁ []
... | false with
  (findᵇ (Data.Bool.not ∘ null)
  ∘ Data.List.map (λ unif → schedule (Data.List.map inj₁ unif) constraints) 
  ∘ catMaybes 
  ∘ Data.List.map (zipMatch at y)) x
... | just r = inj₁ r
... | nothing = inj₂ (record {})
-- ∘ filterᵇ (λ a → (all (λ z → occursᵥ {listOf (listOf mixedConstraint)} {⊤} C Code Constraint z constraints) ∘ collectVarsᵥ C Code Constraint) (_<ᵢ a ⦃ ft ⦄))

-- Checks the call stack for loops

checkLoops :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List Atom
  → Atom
  → ℕ
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) ⊎ ⊤
checkLoops _ [] y n = inj₂ (record {})
checkLoops ⦃ dec ⦄ ⦃ at ⦄ constraints (x ∷ xs) y n with 
  zipMatch at x y Data.Maybe.>>= (λ unif → ((just ∘ schedule (Data.List.map inj₁ unif)) constraints))
... | just result@(_ ∷ _) =
  if n ≡ᵇ 0 
  then inj₁ []
  else 
    if mod n 2 ≡ᵇ 0
    then inj₁ result
    else checkLoops constraints xs y (if isNot x then suc n else n)
... | _ =
  checkLoops constraints xs y (if isNot x then suc n else n)

{-# TERMINATING #-}
checkASP : 
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (ASPAtom Atom 𝒞 Code Constraint)
  → EvalType (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint (ASPUtils Atom 𝒞 Code Constraint × List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint) × List (Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) × Modifier × (ASPAtom Atom 𝒞 Code Constraint))))

-- The intercepter used for ASP. Gets called by eval instead of a recursive call, and allows for injection of additional behaviour
-- In this case, co-SLD resolution, the forall meta predicate and the dynamic chs and loop checks are implemented in here.

{-# TERMINATING #-}
interceptASP :
  ∀ {Atom 𝒞 Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ AtomUtils (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → EvalType (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint (ASPUtils Atom 𝒞 Code Constraint × List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint) × List (Tree ((List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) × Modifier × (ASPAtom Atom 𝒞 Code Constraint))))

checkASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ at (aspU , chs , stack , justification) program goals constraints with checkCHS ⦃ dec ⦄ ⦃ ft ⦄ ⦃ ato ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ aspAtomUtils ⦃ aspU ⦄ ⦄ constraints chs at
... | inj₁ (x ∷ xs) = 
  Data.List.map 
    (λ ((nAspU , nChs , nNewStack , nJustification) , nNewConstraints) → 
       ((nAspU , nChs , nNewStack , node ((x ∷ xs) , provenMod , at) [] ∷ nJustification) , nNewConstraints))
    (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ 
      (aspU , at ∷ chs , stack , []) program goals constraints)                -- CHS success
... | inj₁ [] = []                                                          -- CHS fail
... | inj₂ _ with checkLoops ⦃ dec ⦄ ⦃ ato ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ aspAtomUtils ⦃ aspU ⦄ ⦄ constraints stack at 0                     -- CHS neutral
... | inj₁ [] = []                                                          -- Loop fail
... | inj₁ (x ∷ xs) = 
  Data.List.map 
    (λ ((nAspU , nChs , nNewStack , nJustification) , nNewConstraints) → 
       ((nAspU , nChs , nNewStack , node ([] , chsMod , at) [] ∷ nJustification) , nNewConstraints))
    (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ 
      (aspU , at ∷ chs , stack , []) program goals constraints)                 -- Loop success
... | inj₂ _ = 
  let res = eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄) (aspU , chs , (at ∷ stack) , []) program (atom ⦃ ft ⦄ ⦃ ato ⦄ at ∷ []) constraints in -- Loop neutral
    (concat ∘ 
      Data.List.map 
        (λ ((aspU , chs , newStack , justification) , newConstraints) → 
          Data.List.map (λ ((nAspU , nChs , nNewStack , nJustification) , nNewConstraints) → ((nAspU , nChs , nNewStack , node ([] , noneMod , at) justification ∷ nJustification) , nNewConstraints)) 
            (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , (at ∷ chs) , stack , []) program goals newConstraints))) res

interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , chs , stack , justification) program (constraint cn ∷ goals) constraints = 
  eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄) (aspU , chs , stack , justification) program (constraint cn ∷ goals) constraints
interceptASP {Atom}{C}{Code}{Constraint} (aspU , chs , stack , justification) program (atom (forAll v x) ∷ goals) constraints with collectVarsᵥ {domainExpr} {⊤} C Code Constraint v
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , chs , stack , justification) program (atom (forAll v x) ∷ goals) constraints | (n ∷ _) =
  ASP.dual.maybeToList
    (cForall ⦃ dec ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ n (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , chs , stack , justification) program (atom ⦃ ft ⦄ ⦃ ato ⦄ x ∷ goals) [])
    Data.Maybe.>>= (just ∘ concat ∘ Data.List.map ((λ ((nAspU , nChs , nNewStack , nJustification) , _) → nJustification)))
    Data.Maybe.>>= (λ justif → just (((aspU , chs , stack , justif) , constraints) ∷ [])))
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , chs , stack , justification) program (atom (forAll v x) ∷ goals) constraints | [] =
  []
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , chs , stack , justification) program (atom at ∷ goals) constraints = 
  checkASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ at (aspU , chs , stack , justification) program goals constraints
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , chs , stack , justification) program [] constraints = 
  ((aspU , chs , stack , []) , constraints) ∷ []