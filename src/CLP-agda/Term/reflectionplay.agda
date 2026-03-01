{-# OPTIONS --safe #-}

module Term.reflectionplay where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Data.Bool
open import Data.List
open import Data.Product hiding (map)

_>>=_ : ∀ {A B} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ : ∀ {A B} → TC A → TC B → TC B
m >> n = bindTC m (λ _ → n)

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

mapTC : ∀ {A B} → (A → TC B) → List A → TC (List B)
mapTC f []       = returnTC []
mapTC f (x ∷ xs) = do
  y  ← f x
  ys ← mapTC f xs
  returnTC (y ∷ ys)

------------------------------------------------------------------------
-- Extract parameter count and constructors
------------------------------------------------------------------------

record DataInfo : Set where
  constructor mkDataInfo
  field
    params : Nat
    ctors  : List Name

getDataInfo : Name → TC DataInfo
getDataInfo n = do
  defi ← getDefinition n
  getDataInfo′ defi
  where
    getDataInfo′ : Definition → TC DataInfo
    getDataInfo′ (data-type pars cs) = returnTC (mkDataInfo pars cs)
    getDataInfo′ _ = typeError
      ( strErr "Not a datatype: "
      ∷ nameErr n
      ∷ [] )

------------------------------------------------------------------------
-- Rewrite recursive occurrences
------------------------------------------------------------------------

unArg : ∀ {a} {A : Set a} → Arg A → A
unArg (arg _ x) = x

absName : ∀ {A} → Abs A → String
absName (abs s _) = s

absBody : ∀ {A} → Abs A → A
absBody (abs _ x) = x

rewriteRecursive : Name → Name → Term → Term
rewriteRecursiveArg : Name → Name → Arg Term → Arg Term

rewriteRecursive old new (var x args) = var x (map rewriteRecursiveArg args)
rewriteRecursive old new (con c args) = con c (map rewriteRecursiveArg args)
rewriteRecursive old new (def n args) =
  let n' = if primQNameEquality n old then new else n
  in def n' (map rewriteRecursiveArg args)
rewriteRecursive old new (lam h b) = lam h (abs (absName b) (rewriteRecursive old new (absBody b)))
rewriteRecursive old new (pi a b) = pi (rewriteRecursiveArg a) (abs (absName b) (rewriteRecursive old new (absBody b)))
rewriteRecursive old new (meta m args) = meta m (map rewriteRecursiveArg args)
rewriteRecursive old new (agda-sort s) = agda-sort s
rewriteRecursive old new (lit l) = lit l
rewriteRecursive old new unknown = unknown

-- helper for Arg Term
rewriteRecursiveArg old new (arg i x) = arg i (rewriteRecursive old new x)

------------------------------------------------------------------------
-- Generate Logic datatype (parameter-aware)
------------------------------------------------------------------------
caseDef : Definition → TC (Nat × List Name)
caseDef (data-type p cs) = returnTC (p , cs)
caseDef _ = typeError (strErr "Not a datatype" ∷ [])

deriveLogic : Name → TC Name
deriveLogic n = do
  -- 1. Get type info
  def ← getDefinition n
  let (pars , cs) = caseDef def

  -- 2. Create names for Logic type and var constructor
  let baseStr = primShowQName n
  logicName ← freshName (baseStr ++ "Logic")
  varName   ← freshName ("var" ++ baseStr)

  -- 3. Rewrite constructor types
  tys ← mapTC getType cs
  tys' ← returnTC (map (rewriteRecursive n logicName) tys)

  -- 4. Add var constructor type: ℕ → LogicType
  let varType = el (def (quote Nat) [] `→` def logicName [])

  -- 5. Declare the new datatype
  declareData logicName pars (cs ++ (varName ∷ []))

  defineData logicName 

  returnTC logicName