module Term.types where

open import Data.Bool hiding (not ; _∧_)
open import Data.Char
open import Data.String
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.List
open import Data.Product
open import Data.Sum

open import Term.chatGpt
open import Term.ftUtilsDerivation

open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Effect.Monad using (RawMonad)
open import Agda.Builtin.String
open import Agda.Builtin.Unit


data ℒ (A : Set) : Set where
  _=ℒ_ : A → A → ℒ A
  _≠ℒ_ : A → A → ℒ A

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

data AbstractOrConcrete : Set where
  concr : AbstractOrConcrete
  abstr : AbstractOrConcrete

data Body 
  (A : Set) 
  (val : AbstractOrConcrete → A → Set)
  (Index : Set) 
  (Constraint : (Index → Set)) : Set where
  end  : (functor : A) → val concr functor → Body A val Index Constraint
  endst  : (Σ Index (Dual ∘ Constraint)) → Body A val Index Constraint
  cons : (functor : A) → val concr functor → Body A val Index Constraint → Body A val Index Constraint
  constr : (Σ Index (Dual ∘ Constraint)) → Body A val Index Constraint → Body A val Index Constraint

pattern _• x = end x _
pattern _∧_ x y = cons x _ y
pattern _↼• x = endst x
pattern _↼_ x y = constr x y

data Clause 
  (A : Set) 
  (val : Where → AbstractOrConcrete → A → Set)
  (Index : Set) 
  (Constraint : (Index → Set)) : Set₁ where
  fact : (functor : A)
       → val headOfRule concr functor
       → Clause A val Index Constraint

  rule : (functor : A)
       → val headOfRule concr functor
       → Body A (val bodyOfRule) Index Constraint
       → Clause A val Index Constraint

  _>>_ : Clause A val Index Constraint → Clause A val Index Constraint → Clause A val Index Constraint

  _>>=_ : {B : Set} → ⦃ MakeVar B ⦄ → B → (B → Clause A val Index Constraint) → Clause A val Index Constraint

pattern _• x = fact x _
pattern _:-_ x y = rule x _ y

infix 60 _•
infix 60 _↼•
infixr 50 _∧_
infixr 50 _↼_

infix 30 _:-_

applyVars
  : ∀ {A val Index Constraint}
  → Clause A val Index Constraint
  → ℕ → ℕ × Clause A val Index Constraint
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

--foldExprD = deriveFold exprD
-- ((3 ⦊ nil) ×× ( 4 ⦊ 6 ⦊ (generic 5)))
{-
apply : ∀ {A} → ⦃ FTUtils A ⦄ → Expr A → ℕ → Expr A → Expr A
apply sub x = foldExprD _××_ nil atomic _⦊_ (λ { y → if x ≡ᵇ y then sub else generic y })

breakArgs : ∀ {A} → ⦃ FTUtils A ⦄ → Expr A → List (Expr A)
breakArgs = proj₂ ∘ (foldExprD 
          (λ {(x , _) (y , _) → (_××_ x y , (x ∷ y ∷ []))})
          (nil , [])
          (λ { y → (atomic y , []) })
          (λ {(x , _) (y , _) → (_⦊_ x y , (x ∷ y ∷ []))})
          (λ { y → (generic y , []) }))
-}

{-
Generics.Reflection.badconvert
(Generics.Reflection.mkHD
 ((var (λ PV → tt) ⊗ var (λ PV → tt)) ∷
  (π ("l" , arg-info visible defaultModality)
   (λ PV → ListLogic GenericVar)
   (var (λ PV → tt) ⊗
    π ("l₁" , arg-info visible defaultModality)
    (λ PV → ListLogic (GenericVar ×Logic GenericVar))
    (var (λ PV → tt)))
   ∷ (var (λ PV → tt) ∷ (var (λ PV → tt) ∷ []))))
 ("not" ∷ "dupli" ∷ "⊤" ∷ "false" ∷ []) Term.types.constr
 Term.types.split Term.types.split∘constr Term.types.constr∘split
 Term.types.wf)
 -}

record Permission (Index : Set) (Code : (Index → Set)) (Constraint : (Index → Set)) : Set where
  field
    getPermission : (i : Index) → (Σ Index (ℒ ∘ Code)) → Maybe ((ℒ ∘ Code) i)
    getPermissionCustom : (i : Index) → (Σ Index (Dual ∘ Constraint)) → Maybe ((Dual ∘ Constraint) i)
open Permission ⦃...⦄ public

record Solver (Index : Set) (Code : (Index → Set)) (Constraint : (Index → Set)) : Set where
  field
    solve : (i : Index)
     → List ((Σ Index (ℒ ∘ Code)) ⊎ (Σ Index (Dual ∘ Constraint)))
     → (Maybe ∘ List) (List ((Σ Index (ℒ ∘ Code)) ⊎ (Σ Index (Dual ∘ Constraint))))
open Solver ⦃...⦄ public

--interpret : ∀ {A val C} → ⦃ FTUtils A ⦄ → (Index : Set) → (Code : (Index → Set)) → (i : Index) → Clause A val C → Clause A val C → ⊤
--interpret _ _ _ (fact f _) (fact g _) = {!   !}