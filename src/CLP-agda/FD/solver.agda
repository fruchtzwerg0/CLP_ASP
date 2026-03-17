module FD.solver where


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

data Expr : Set where
  Lit : ℕ    → Expr
  Var : String → Expr
  Add : Expr   → Expr → Expr
  Sub : Expr   → Expr → Expr
  Mul : Expr   → Expr → Expr
  Div : Expr   → Expr → Expr

data Constraint : Set where
  Lt  : Expr → Expr → Constraint
  Gt  : Expr → Expr → Constraint
  Leq : Expr → Expr → Constraint
  Geq : Expr → Expr → Constraint
  Eq  : Expr → Expr → Constraint
  Neq : Expr → Expr → Constraint

Store : Set
Store = List Constraint

Binding : Set
Binding = String × ℕ

{-# FOREIGN GHC
  import System.IO.Unsafe (unsafePerformIO)
  import FDSolver
  import Data.Text (Text, unpack, pack)

  toHsExpr :: Expr -> FDSolver.Expr
  toHsExpr (Lit n)     = FDSolver.Lit (fromIntegral n)
  toHsExpr (Var v)     = FDSolver.Var (unpack v)
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

  fromHsBinding :: (String, Int) -> (Text, Integer)
  fromHsBinding (v, n) = (pack v, fromIntegral n)

  agdaIsSatisfiable :: [Constraint] -> IO Bool
  agdaIsSatisfiable store = isSatisfiable (toHsStore store)

  agdaLabeling :: [Constraint] -> IO (Maybe [(Text, Integer)])
  agdaLabeling store = do
    result <- labeling (toHsStore store)
    return (fmap (map fromHsBinding) result)
#-}

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

postulate
  isSatisfiablePure : Store → Bool
  labelingPure      : Store → Maybe (List Binding)

{-# COMPILE GHC isSatisfiablePure =
    \store -> unsafePerformIO (agdaIsSatisfiable store) #-}
{-# COMPILE GHC labelingPure =
    \store -> unsafePerformIO (agdaLabeling store) #-}

toTerm : FD → Expr
toTerm (x ＃+ y) = Add (toTerm x) (toTerm y)
toTerm (x ＃- y) = Sub (toTerm x) (toTerm y)
toTerm (x ＃* y) = Mul (toTerm x) (toTerm y)
toTerm (div x y) = Div (toTerm x) (toTerm y)
toTerm zero = Lit zero
toTerm (suc x) = Lit (suc zero)
toTerm (varFD x) = Lit zero

toConstraint : ℒ FD ⊎ Dual ℒFD → Constraint
toConstraint (inj₁ (x =ℒ y)) = Eq (toTerm x) (toTerm y)
toConstraint (inj₁ (x ≠ℒ y)) = Neq (toTerm x) (toTerm y)
toConstraint (inj₂ (default (x ≤FD y))) = Leq (toTerm x) (toTerm y)
toConstraint (inj₂ (dual (x ≤FD y))) = Gt (toTerm x) (toTerm y)
toConstraint (inj₂ (default (x ≥FD y))) = Geq (toTerm x) (toTerm y)
toConstraint (inj₂ (dual (x ≥FD y))) = Lt (toTerm x) (toTerm y)

fdSolve : 
  List (ℒ FD ⊎ Dual ℒFD)
  → (List ∘ List) (ℒ FD ⊎ Dual ℒFD)
fdSolve constraints = 
    ((λ x → if x then constraints ∷ [] else []) 
    ∘ isSatisfiablePure 
    ∘ Data.List.map toConstraint) constraints