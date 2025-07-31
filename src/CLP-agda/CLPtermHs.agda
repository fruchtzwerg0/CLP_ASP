module CLPtermHs where

open import Term.types
open import Term.solver
open import Common.types
open import Common.solver
open import Common.utilities
open import CLP.clp
open import Data.String 
  using (String; _==_)
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst)
open import Data.List 
  using (List; []; _∷_; _++_; any; all; map; foldl; length; zip; zipWith; concat)
open import Data.Bool
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.Maybe 
  using (Maybe; just; nothing; map)
open import Data.Product 
  using (_×_; _,_)

-- Very ugly and boilerplaty, but necessary for Haskell interface
-- Genericity gets completely lost here (Term hardcoded everywhere),
-- but haven't found another solution (Cannot translate the universe genericity into Haskell)

mutual
  data LogicVarForHs : Set where
    varForHs : Maybe ℕ → LogicVarForHs
    constForHs : TermForHs → LogicVarForHs

  data TermForHs : Set where
    atomTForHs : String → List LogicVarForHs → TermForHs

data ExprTerm : Set where
  domainExprTerm : LogicVarForHs → ExprTerm

data AtomTerm : Set where
  mkAtomTerm : String → List ExprTerm → AtomTerm

data ℒTerm : Set where
  eqTerm : ExprTerm → ExprTerm → ℒTerm

data LiteralTerm : Set where
  atomLiteralTerm : AtomTerm → LiteralTerm
  eqLiteralTerm   : ℒTerm → LiteralTerm

data ClauseTerm : Set where
  mkClauseTerm : AtomTerm → List LiteralTerm → ClauseTerm

{-# TERMINATING #-}
fromLogicVarForHs : LogicVarForHs → LogicVar (Term LogicVar)
fromTermForHs : TermForHs → Term LogicVar

fromLogicVarForHs (varForHs x) = var x
fromLogicVarForHs (constForHs t) = const (fromTermForHs t)

fromTermForHs (atomTForHs s args) = atomT s (Data.List.map fromLogicVarForHs args)

fromExprTerm : ExprTerm → Expr term
fromExprTerm (domainExprTerm x) = domainExpr (fromLogicVarForHs x)

fromAtomTerm : AtomTerm → Atom term
fromAtomTerm (mkAtomTerm name args) = mkAtom name (Data.List.map fromExprTerm args)

fromℒTerm : ℒTerm → ℒ term
fromℒTerm (eqTerm e₁ e₂) = fromExprTerm e₁ =ℒ fromExprTerm e₂

fromLiteralTerm : LiteralTerm → Literal term
fromLiteralTerm (atomLiteralTerm a) = atomLiteral (fromAtomTerm a)
fromLiteralTerm (eqLiteralTerm l)   = 𝓁Literal (fromℒTerm l)

fromClauseTerm : ClauseTerm → Clause term
fromClauseTerm (mkClauseTerm head body) = fromAtomTerm head :- Data.List.map fromLiteralTerm body

data SubstTerm : Set where
  substTerm : ℕ → LogicVarForHs → SubstTerm

data EvalTerm : Set where
  yesAllTerm : List (List SubstTerm) → EvalTerm
  yesTerm : List SubstTerm → EvalTerm
  noTerm  : EvalTerm

{-# TERMINATING #-}
toLogicVarForHs : LogicVar (Term LogicVar) → LogicVarForHs
toTermForHs : Term LogicVar → TermForHs

toLogicVarForHs (var x)     = varForHs x
toLogicVarForHs (const tm)  = constForHs (toTermForHs tm)

toTermForHs (atomT s args)  = atomTForHs s (Data.List.map toLogicVarForHs args)

toSubstTerm : Subst term → List SubstTerm
toSubstTerm subst = Data.List.map (λ (x , y) → substTerm x (toLogicVarForHs y)) subst

toEvalTerm : {findAll : Bool} → if findAll then List (Subst term) else Maybe (Subst term) → EvalTerm
toEvalTerm {false} (just subst) = yesTerm (toSubstTerm subst)
toEvalTerm {true} subst = yesAllTerm (Data.List.map toSubstTerm subst)
toEvalTerm {false} nothing      = noTerm

evalTerm : (program : List (ClauseTerm)) → (left : List (LiteralTerm)) → Bool → EvalTerm
evalTerm program left findAll = toEvalTerm (eval (Data.List.map fromClauseTerm program) (Data.List.map fromLiteralTerm left) [] findAll [])

{-# FOREIGN GHC {-# LANGUAGE DeriveDataTypeable #-} #-}

{-# FOREIGN GHC
  import Data.Data (Data)
  import Data.Typeable (Typeable)
  import Data.Text (Text)

  data TermHs
    = MkAtomTHs Text [LogicVarHs]
    deriving (Show, Eq, Data, Typeable)

  data LogicVarHs
    = MkVarHs (Maybe Integer)
    | MkConstHs TermHs
    deriving (Show, Eq, Data, Typeable)

  -- ExprTerm
  data ExprTermHs
    = MkExprTermHs LogicVarHs
    deriving (Show, Eq, Data, Typeable)

  -- AtomTerm
  data AtomTermHs
    = MkAtomTermHs Text [ExprTermHs]
    deriving (Show, Eq, Data, Typeable)

  -- ℒTerm
  data ℒTerm
    = EqTermHs ExprTermHs ExprTermHs
    deriving (Show, Eq, Data, Typeable)

  -- LiteralTerm
  data LiteralTermHs
    = AtomLiteralTermHs AtomTermHs
    | EqLiteralTermHs ℒTerm
    deriving (Show, Eq, Data, Typeable)

  -- ClauseTerm
  data ClauseTermHs
    = MkClauseTermHs AtomTermHs [LiteralTermHs]
    deriving (Show, Eq, Data, Typeable)

  -- SubstTerm
  data SubstTermHs
    = SubstTermHs Integer LogicVarHs
    deriving (Show, Eq, Data, Typeable)

  -- EvalTerm
  data EvalTermHs
    = YesAllTermHs [[SubstTermHs]]
    | YesTermHs [SubstTermHs]
    | NoTermHs
    deriving (Show, Eq, Data, Typeable)
#-}

{-# COMPILE GHC TermForHs = data TermHs (MkAtomTHs) #-}
{-# COMPILE GHC LogicVarForHs = data LogicVarHs (MkVarHs | MkConstHs) #-}
{-# COMPILE GHC ExprTerm = data ExprTermHs (MkExprTermHs) #-}
{-# COMPILE GHC AtomTerm = data AtomTermHs (MkAtomTermHs) #-}
{-# COMPILE GHC ℒTerm = data ℒTerm (EqTermHs) #-}
{-# COMPILE GHC LiteralTerm = data LiteralTermHs (AtomLiteralTermHs | EqLiteralTermHs) #-}
{-# COMPILE GHC ClauseTerm = data ClauseTermHs (MkClauseTermHs) #-}
{-# COMPILE GHC SubstTerm = data SubstTermHs (SubstTermHs) #-}
{-# COMPILE GHC EvalTerm = data EvalTermHs (YesAllTermHs | YesTermHs | NoTermHs) #-}

{-# COMPILE GHC evalTerm as evalTermAgda #-}