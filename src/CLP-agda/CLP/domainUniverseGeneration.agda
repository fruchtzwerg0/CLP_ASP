{-# OPTIONS --safe #-}

module CLP.domainUniverseGeneration where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (equal; _≟_)
open import Data.List
open import Data.Product hiding (map)

_>>=_ : {A B : Set} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ : {A B : Set} → TC A → TC B → TC B
m >> n = bindTC m (λ _ → n)

mapTC : {A B : Set} → (A → TC B) → List A → TC (List B)
mapTC f [] = returnTC []
mapTC f (x ∷ xs) =
  f x >>= λ y →
  mapTC f xs >>= λ ys →
  returnTC (y ∷ ys)

isData : Definition → Bool
isData (data-type _ _) = true
isData _ = false

dataPars : Definition → Nat
dataPars (data-type pars _) = pars
dataPars _ = 0

getInductiveArity : Name → TC Nat
getInductiveArity n =
  getDefinition n >>= λ d →
  returnTC (dataPars d)

argInfo : ArgInfo
argInfo = arg-info visible (modality relevant quantity-ω)

mkArg : Term → Arg Term
mkArg t = arg argInfo t

makeConstructor :
  Name   -- constructor name
  → Name -- source type
  → Name -- datatype name
  → TC (Σ Name (λ _ → Type))
makeConstructor c srcType myC =

  getInductiveArity srcType >>= λ arity →

  let argTerms = replicate arity (def myC [])
      args     = map mkArg argTerms
  in

  returnTC
    ( c
    , foldr
        (λ a t → pi a (abs "_" t))
        (def myC [])
        args
    )

makeUniverse :
  Name → List (Name × Name) → TC ⊤
makeUniverse myC consAndsrcTypes =

  mapTC
    (λ (c , t) → makeConstructor c t myC)
    consAndsrcTypes
  >>= λ constructors →

  declareData myC 0 (agda-sort (lit 0)) >>
  defineData myC constructors

range : Nat → List Nat
range zero    = []
range (suc n) = range n ++ [ n ]

countPis : Type → Nat
countPis (pi _ (abs _ t)) = suc (countPis t)
countPis _                = 0

getConstructorArity' : Name → TC Nat
getConstructorArity' c =
  getType c >>= λ ty →
  returnTC (countPis ty)

makeDecoder
  : Name
  → Name
  → List (Name × Name)
  → TC ⊤
makeDecoder decName myCName consTarget = do
  -- NO freshName here!
  let ty = pi (mkArg (def myCName []))
               (abs "_" (agda-sort (lit 0)))
  declareDef (arg argInfo decName) ty
  clauses ← mapTC
    (λ (c , tgtName) → do
       arity ← getConstructorArity' c
       let tel : Telescope
           tel = foldr (λ _ acc → ("_" , arg argInfo (def myCName [])) ∷ acc) [] (reverse (range arity))
       let lhsArgs : List (Arg Pattern)
           lhsArgs = map (λ i → arg argInfo (Pattern.var (arity - 1 - i))) (range arity)
           lhs     = arg argInfo (Pattern.con c lhsArgs)
       rhs ← if arity == 0
              then returnTC (def tgtName [])
              else
                let rhsArgs = foldr (λ i acc → mkArg (def decName (mkArg (var i []) ∷ [])) ∷ acc) [] (reverse (range arity))
                in returnTC (def tgtName rhsArgs)
       returnTC (clause tel (lhs ∷ []) rhs)
    )
    consTarget
  defineFun decName clauses

mkInstanceArg : Term → Arg Term
mkInstanceArg t = arg (arg-info instance′ (modality relevant quantity-ω)) t

makeMapper
  : Name               -- function name (bound by unquoteDecl)
  → Name               -- MyC
  → Name               -- decoder ⟦_⟧
  → Name               -- typeclass F (e.g. FTUtils or DecEq)
  → List (Name × Name) -- (constructor , implementation)
  → TC ⊤
makeMapper funName myCName decoderName F consImpls = do

  let ty = pi (mkArg (def myCName []))
               (abs "c" (def F
                 (mkArg (def decoderName (mkArg (var 0 []) ∷ [])) ∷ [])))
  declareDef (arg argInfo funName) ty

  clauses ← mapTC
    (λ (c , impl) → do
       arity ← getConstructorArity' c

       let tel : Telescope
           tel = foldr (λ _ acc → ("_" , arg argInfo (def myCName [])) ∷ acc)
                       [] (reverse (range arity))

       let lhsArgs : List (Arg Pattern)
           lhsArgs = map (λ i → arg argInfo (Pattern.var (arity - 1 - i)))
                         (range arity)
           lhs = arg argInfo (Pattern.con c lhsArgs)

       let mkRecArg : Nat → Arg Term
           mkRecArg i = mkInstanceArg (def funName (mkArg (var i []) ∷ []))

       rhs ← if arity == 0
              then returnTC (def impl [])
              else
                let recArgs = foldr (λ i acc → mkRecArg i ∷ acc)
                                    [] (reverse (range arity))
                in returnTC (def impl recArgs)

       returnTC (clause tel (lhs ∷ []) rhs)
    )
    consImpls

  defineFun funName clauses