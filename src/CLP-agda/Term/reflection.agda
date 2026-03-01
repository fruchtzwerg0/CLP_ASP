module Term.reflection where

open import Agda.Builtin.Reflection
open import Reflection hiding (name; Type)
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Data.Char as Char
open import Data.String as String
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.Bool
open import Data.List
open import Agda.Builtin.Sigma

open import Agda.Primitive

open import Agda.Builtin.Reflection

validateType : Name → TC ⊤
validateType n = do
  def ← getDefinition n
  case def of
    data-type _ _ → pure tt
    _ → typeError (strErr "Not a datatype: " ∷ nameErr n ∷ [])

macro
  newConstraintDomainSystem : Term → TC ⊤
  newConstraintDomainSystem specTerm = do

    spec ← evalSpec specTerm

    validateAtom spec
    validateAllTypes spec

    forM (types spec) generateLogicType
    forM (types spec) generateConstraintType

    generateIndexType spec
    generateInterpretation spec
    generateInstances spec

    unify (quoteTerm tt) (quoteTerm tt)