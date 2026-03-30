module FD.solver where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Data.Bool hiding (not ; _∧_)
open import Data.Char
open import Data.String hiding (head; _++_)
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.List hiding (head)
open import Data.Product
open import Data.Sum
open import Function.Base

open import FD.domain
open import CLP.types

-- Expressions
data Expr : Set where
  Lit : Int → Expr
  Var : ℕ → Expr
  Add : Expr → Expr → Expr
  Sub : Expr → Expr → Expr
  Mul : Expr → Expr → Expr
  Div : Expr → Expr → Expr

-- Constraints
data Constraint : Set where
  Lt  : Expr → Expr → Constraint
  Gt  : Expr → Expr → Constraint
  Leq : Expr → Expr → Constraint
  Geq : Expr → Expr → Constraint
  Eq  : Expr → Expr → Constraint
  Neq : Expr → Expr → Constraint

Store : Set
Store = List Constraint

-- Agda Binding record mirrors the new Haskell type
record Binding : Set where
  constructor MkBinding
  field
    var : ℕ
    val : Int

-- Foreign Haskell interface
{-# FOREIGN GHC
  import System.IO.Unsafe (unsafePerformIO)
  import FDSolver
  import Data.Text (Text, pack, unpack)

  toHsExpr :: Expr -> FDSolver.Expr
  toHsExpr (Lit n)     = FDSolver.Lit (fromIntegral n)
  toHsExpr (Var v)     = FDSolver.Var v
  toHsExpr (Add a b)   = FDSolver.Add (toHsExpr a) (toHsExpr b)
  toHsExpr (Sub a b)   = FDSolver.Sub (toHsExpr a) (toHsExpr b)
  toHsExpr (Mul a b)   = FDSolver.Mul (toHsExpr a) (toHsExpr b)
  toHsExpr (Div a b)   = FDSolver.Div (toHsExpr a) (toHsExpr b)

  toHsConstraint :: Constraint -> FDSolver.Constraint
  toHsConstraint (Lt  a b) = FDSolver.Lt  (toHsExpr a) (toHsExpr b)
  toHsConstraint (Gt  a b) = FDSolver.Gt  (toHsExpr a) (toHsExpr b)
  toHsConstraint (Leq a b) = FDSolver.Leq (toHsExpr a) (toHsExpr b)
  toHsConstraint (Geq a b) = FDSolver.Geq (toHsExpr a) (toHsExpr b)
  toHsConstraint (Eq  a b) = FDSolver.Eq  (toHsExpr a) (toHsExpr b)
  toHsConstraint (Neq a b) = FDSolver.Neq (toHsExpr a) (toHsExpr b)

  toHsStore :: [Constraint] -> FDSolver.Store
  toHsStore = map toHsConstraint

  fromHsBinding :: FDSolver.Binding -> Binding
  fromHsBinding (FDSolver.MkBinding v n) = MkBinding { var = v, val = n }

  agdaIsSatisfiable :: [Constraint] -> IO Bool
  agdaIsSatisfiable store = FDSolver.isSatisfiable (toHsStore store)

  agdaLabeling :: [Constraint] -> IO (Maybe [Binding])
  agdaLabeling store = do
    result <- FDSolver.labeling (toHsStore store)
    case result of
      Nothing -> return Nothing
      Just bs -> return (Just (map fromHsBinding bs))
#-}

-- Compile directives to use the Haskell types
{-# COMPILE GHC Expr
    = data FDSolver.Expr
      ( FDSolver.Lit
      | FDSolver.Var
      | FDSolver.Add
      | FDSolver.Sub
      | FDSolver.Mul
      | FDSolver.Div
      ) #-}

{-# COMPILE GHC Constraint
    = data FDSolver.Constraint
      ( FDSolver.Lt
      | FDSolver.Gt
      | FDSolver.Leq
      | FDSolver.Geq
      | FDSolver.Eq
      | FDSolver.Neq
      ) #-}

{-# COMPILE GHC Binding
    = data FDSolver.Binding
      ( FDSolver.MkBinding )
#-}

-- Pure wrappers for use inside Agda
postulate
  isSatisfiablePure : Store → Bool
  labelingPure      : Store → Maybe (List Binding)

{-# COMPILE GHC isSatisfiablePure =
    \store -> unsafePerformIO (agdaIsSatisfiable store) #-}
{-# COMPILE GHC labelingPure =
    \store -> unsafePerformIO (agdaLabeling store) #-}

-- FD → Expr translation
toTerm : FD → Expr
toTerm (x ＃+ y) = Add (toTerm x) (toTerm y)
toTerm (x ＃- y) = Sub (toTerm x) (toTerm y)
toTerm (x ＃* y) = Mul (toTerm x) (toTerm y)
toTerm (div x y) = Div (toTerm x) (toTerm y)
toTerm (＃ x)     = Lit x
toTerm (varFD x)  = Var x

toConstraint : ℒ FD ⊎ Dual ℒFD → Constraint
toConstraint (inj₁ (x =ℒ y)) = Eq  (toTerm x) (toTerm y)
toConstraint (inj₁ (x ≠ℒ y)) = Neq (toTerm x) (toTerm y)
toConstraint (inj₂ (default (x ≤FD y))) = Leq (toTerm x) (toTerm y)
toConstraint (inj₂ (dual (x ≤FD y)))    = Gt  (toTerm x) (toTerm y)
toConstraint (inj₂ (default (x ≥FD y))) = Geq (toTerm x) (toTerm y)
toConstraint (inj₂ (dual (x ≥FD y)))    = Lt  (toTerm x) (toTerm y)

fdSolve :
  List (ℒ FD ⊎ Dual ℒFD)
  → (List ∘ List) (ℒ FD ⊎ Dual ℒFD)
fdSolve constraints =
  ((λ x → if x then constraints ∷ [] else [])
  ∘ isSatisfiablePure
  ∘ Data.List.map toConstraint) constraints
  
maybeToList : {A : Set} → Maybe (List A) → List A
maybeToList nothing  = []
maybeToList (just x) = x

labeling : 
  List (ℒ FD ⊎ Dual ℒFD)
  → List ((ℕ × FD) ⊎ (ℕ × FD))
labeling constraints =
  (Data.List.map (λ (MkBinding va vl) → inj₁ (va , ＃ vl))
  ∘ maybeToList ∘ labelingPure
  ∘ Data.List.map toConstraint) constraints