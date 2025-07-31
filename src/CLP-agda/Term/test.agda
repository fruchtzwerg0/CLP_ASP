module Term.test where

open import Term.types
open import Term.solver
open import Common.types
open import Common.solver
open import Common.utilities
open import CLP.clp
open import Views.find
open import Views.findall
open import Data.Bool
open import Data.String 
  using (String; _==_)
open import Data.Nat 
  using (ℕ; suc; _≡ᵇ_; _⊔_; _⊓_; _+_)
open import Data.List 
  using (List; []; _∷_)
open import Data.Maybe 
  using (Maybe; just; nothing; map)
open import Data.Product 
  using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl)

-- Some type-level unit tests

ancestor_program : List (Clause term)
ancestor_program =
    (mkAtom "parent"
  (domainExpr (const (atomT "alice" [])) ∷
    domainExpr (const (atomT "bob" [])) ∷ [])
  :- [])
  ∷
  (mkAtom "parent"
  (domainExpr (const (atomT "bob" [])) ∷
    domainExpr (const (atomT "charlie" [])) ∷ [])
  :- [])
  ∷
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷ domainExpr (var (just 2)) ∷ [])
  :-
  (atomLiteral
    (mkAtom "parent"
    (domainExpr (var (just 1)) ∷ domainExpr (var (just 2)) ∷ []))
    ∷ []))
  ∷
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷ domainExpr (var (just 2)) ∷ [])
  :-
  (atomLiteral
    (mkAtom "parent"
    (domainExpr (var (just 1)) ∷ domainExpr (var (just 3)) ∷ []))
    ∷
    atomLiteral
    (mkAtom "ancestor"
    (domainExpr (var (just 3)) ∷ domainExpr (var (just 2)) ∷ []))
    ∷ []))
  ∷ []

evalUnitTest0 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (const (atomT "charlie" [])) ∷ []))
  ∷ []) [] false [] ≡ just (( 1 , const (atomT "bob" []) ) ∷ []))
evalUnitTest0 = refl

evalUnitTest1 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (const (atomT "charlie" [])) ∷ []))
  ∷ []) [] true [] ≡ ((( 1 , const (atomT "bob" []) ) ∷ []) ∷ (( 1 , const (atomT "alice" []) ) ∷ []) ∷ []))
evalUnitTest1 = refl

evalUnitTest2 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (var (just 2)) ∷ []))
  ∷ []) [] false [] ≡ just (( 1 , const (atomT "alice" []) ) ∷ ( 2 , const (atomT "bob" [])) ∷ []))
evalUnitTest2 = refl

evalUnitTest3 : 
  (eval ancestor_program (atomLiteral
  (mkAtom "ancestor"
  (domainExpr (var (just 1)) ∷
    domainExpr (var (just 2)) ∷ []))
  ∷ []) [] true [] ≡ (( 1 , const (atomT "alice" []) ) ∷ ( 2 , const (atomT "bob" [])) ∷ [])
   ∷ (( 1 , const (atomT "bob" []) ) ∷ ( 2 , const (atomT "charlie" [])) ∷ [])
   ∷ (( 1 , const (atomT "alice" []) ) ∷ ( 2 , const (atomT "charlie" [])) ∷ []) ∷ [])
evalUnitTest3 = refl

unifyUnitTest0 : 
  (unify (
      (domainExpr (var (just 3)) =ℒ domainExpr (const (atomT "bob" [])))
    ∷ (domainExpr (var (just 2)) =ℒ domainExpr (const (atomT "alice" [])))
    ∷ (domainExpr (var (just 1)) =ℒ domainExpr (var (just 3)))
    ∷ (domainExpr (const (atomT "alice" [])) =ℒ domainExpr (var (just 2)))
    ∷ []) ≡ 
      just (
      (3 , const (atomT "bob" []))
    ∷ (2 , const (atomT "alice" []))
    ∷ (1 , const (atomT "bob" []))
    ∷ []))
unifyUnitTest0 = refl
