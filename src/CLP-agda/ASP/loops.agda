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
          aspShow .Generics.show (chk a b c) = "chk "

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
  → ⦃ AtomUtils Atom 𝒞 Code Constraint ⦄
  → ⦃ ConstraintUtils 𝒞 Code Constraint ⦄
  → ⦃ ValueUtils 𝒞 Code Constraint ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → ⦃ ASPUtils Atom 𝒞 Code Constraint ⦄
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List Atom
  → Atom
  → Bool ⊎ ⊤
checkCHS ⦃ dec ⦄ ⦃ at ⦄ constraints x y with 
  (any (Data.Bool.not ∘ null) ∘ Data.List.map (schedule ∘ concat ∘ Data.List.map (addToConstraintStore constraints) ∘ Data.List.map inj₁) ∘ catMaybes ∘ Data.List.map (zipMatch at (toggle y))) x
... | true = inj₁ false
... | false with
  (any (Data.Bool.not ∘ null) ∘ Data.List.map (schedule ∘ concat ∘ Data.List.map (addToConstraintStore constraints) ∘ Data.List.map inj₁) ∘ catMaybes ∘ Data.List.map (zipMatch at y)) x
... | true = inj₁ true
... | false = inj₂ (record {})

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
  zipMatch at x y Data.Maybe.>>= (just ∘ schedule ∘ concat ∘ Data.List.map (addToConstraintStore constraints) ∘ Data.List.map inj₁)
... | just result =
  if n ≡ᵇ 0 
  then inj₁ []
  else 
    if mod n 2 ≡ᵇ 0
    then inj₁ result
    else checkLoops constraints xs y (if isNot x then suc n else n)
... | nothing =
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
  → EvalType (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint (ASPUtils Atom 𝒞 Code Constraint × Show Atom × List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint) × String)

addToJustification : 
  ∀ {Atom 𝒞 Code Constraint}
  → ℕ
  → ASPAtom Atom 𝒞 Code Constraint
  → ⦃ Show (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → ⦃ FTUtils (ASPAtom Atom 𝒞 Code Constraint) ⦄
  → (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → String
addToJustification {_}{C}{Code}{Constraint} n at ⦃ sh ⦄ ⦃ inst ⦄ constraints = "\n" Data.String.++ (Data.String.concat ∘ replicate n) " " Data.String.++ Generics.show ⦃ sh ⦄ at Data.String.++ "[" Data.String.++ (joinWith "; " ∘ Data.List.map (formatOutput false (collectVarsᵥ {atom} C Code Constraint (_<ᵢ at ⦃ inst ⦄)))) constraints Data.String.++ "]"

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
  → EvalType (ASPAtom Atom 𝒞 Code Constraint) 𝒞 Code Constraint (ASPUtils Atom 𝒞 Code Constraint × Show Atom × List (ASPAtom Atom 𝒞 Code Constraint) × List (ASPAtom Atom 𝒞 Code Constraint) × String)

checkASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ at (aspU , sho , chs , stack , justification) program goals constraints with checkCHS ⦃ dec ⦄ ⦃ ato ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ aspAtomUtils ⦃ aspU ⦄ ⦄ constraints chs at
... | inj₁ true = ((aspU , sho , chs , stack , justification) , constraints) ∷ []                    -- CHS success
... | inj₁ false = []                    -- CHS fail
... | inj₂ _ with checkLoops ⦃ dec ⦄ ⦃ ato ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ aspAtomUtils ⦃ aspU ⦄ ⦄ constraints stack at 0                     -- CHS neutral
... | inj₁ [] = []                                                                      -- Loop fail
... | inj₁ (x ∷ xs) = ((aspU , sho , chs , stack , justification) , x ∷ xs) ∷ []                     -- Loop success
... | inj₂ _ = 
  let res = eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄) (aspU , sho , chs , (at ∷ stack) , justification Data.String.++ addToJustification ((suc ∘ length) stack) at ⦃ aspShow ⦃ sho ⦄ ⦄ ⦃ ft ⦄ constraints) program (atom ⦃ ft ⦄ ⦃ ato ⦄ at ∷ []) constraints in -- Loop neutral
    (concat ∘ Data.List.map (λ ((aspU , sho , chs , stack , justification) , ans) → interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , (at ∷ chs) , stack , justification) program goals ans)) res

interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , chs , stack , justification) program (constraint cn ∷ goals) constraints = 
  eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄) (aspU , sho , chs , stack , justification) program (constraint cn ∷ goals) constraints
interceptASP {Atom}{C}{Code}{Constraint} (aspU , sho , chs , stack , justification) program (atom (forAll v x) ∷ goals) constraints with collectVarsᵥ {domainExpr} {⊤} C Code Constraint v
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , chs , stack , justification) program (atom (forAll v x) ∷ goals) constraints | (n ∷ _) =
  if cForall ⦃ dec ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ solv ⦄ ⦃ sched ⦄ ⦃ aspAtomUtils ⦃ aspU ⦄ ⦄ n (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , chs , stack , justification) program (atom ⦃ ft ⦄ ⦃ ato ⦄ x ∷ goals) [])
  then interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , chs , stack , justification) program goals constraints
  else []
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , chs , stack , justification) program (atom (forAll v x) ∷ goals) constraints | [] =
  []
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (aspU , sho , chs , stack , justification) program (atom at ∷ goals) constraints = 
  checkASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ at (aspU , sho , chs , stack , justification) program goals constraints
interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ x y [] z = 
  eval ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄ (interceptASP ⦃ dec ⦄ ⦃ ft ⦄ ⦃ cns ⦄ ⦃ val ⦄ ⦃ ato ⦄ ⦃ solv ⦄ ⦃ sched ⦄) x y [] z