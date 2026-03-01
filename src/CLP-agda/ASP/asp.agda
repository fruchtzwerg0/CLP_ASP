module ASP.asp where


data AspRule (A : Set) : Set where
  not : A → AspRule A

removeHeadUnification : {c : 𝒞} → List (Expr c) → List (Σ (Expr c) Maybe )
removeHeadUnification = foldr (λ { acc arg → if isVar arg ∧ elem arg acc then (suc (maxVarᵥ acc)) ∷ acc else arg ∷ acc }) []

count : ℕ → List ℕ
count (suc x) = x ∷ count x
count zero = []

getNextFreeClauseName : String → ℕ → List (Clause c) → String
getNextFreeClauseName base zero program = if (_≡ᵇ_ 0 ∘ length ∘ filter (λ { (mkAtom name _ :- _) →  base ≡ᵇ name})) program then base else getNextFreeClauseName (base ++ "_") program
getNextFreeClauseName base (suc n) program = if (_≡ᵇ_ 0 ∘ length ∘ filter (λ { (mkAtom name _ :- _) →  base ≡ᵇ name})) program then getNextFreeClauseName base n program else getNextFreeClauseName (base ++ "_") program

unfoldr : {A B : Set} → (B → Maybe (A × B)) → B → List A
unfoldr f seed with f seed
... | nothing        = []
... | just (x , seed') = x ∷ unfoldr f seed'

makeTopLevelBody : {c : 𝒞} → ℕ → ℕ → List (Atom c)
makeTopLevelBody (suc x) argLength = not (mkAtom (getNextFreeClauseName x name) ((count ∘ length) argLength))

without : {A : Set} → (A → A → Dec (A ≡ A)) → List A → List A → List A
without _≟_ xs ys = filter (λ x → not (elem _≟_ x ys)) xs

makeParamUnificationExplicit : {c : 𝒞} → List (Expr c) → List (ℒ c)
makeParamUnificationExplicit ((domainExpr (const x)) ∷ xs) = ((const x) =ℒ ((suc ∘ maxVarᵥ) ((domainExpr (const x)) ∷ xs))) ∷ makeParamUnificationExplicit xs
makeParamUnificationExplicit ((domainExpr (var x)) ∷ xs) = makeParamUnificationExplicit xs
makeParamUnificationExplicit [] = []

collectVarsForForAll : {c : 𝒞} → Clause c → List ℕ
collectVarsForForAll (mkAtom name args :- body) = 
  without _≟_ 
    (collectVarsᵥ (body ++ map 𝓁Literal (makeParamUnificationExplicit args)))
    (collectVarsᵥ (filter isVar args ++ map (λ { (_ =ℒ right) → right }) makeParamUnificationExplicit args))

negateLiteral : {c : 𝒞} → Literal c → Literal c
negateLiteral (atomLiteral atom) = not (atomLiteral atom)
negateLiteral (𝓁Literal (l =ℒ r)) = 𝓁Literal (l ≠ℒ r)

buildNegatedBody : {c : 𝒞} → ℕ → List (Literal c) → List (Literal c)
buildNegatedBody (suc n) lit = negateLiteral lit ∷ buildNegatedBody n
buildNegatedBody (zero) lit = lit ∷ []

makeFreeVarArgs : List ℕ → ℕ → List ℕ
makeFreeVarArgs l (suc x) = (just ∘ suc ∘ maxVarᵥ) l ∷ makeFreeVarArgs l x
makeFreeVarArgs l zero = []

applyDeMorgan : {c : 𝒞} → ℕ → Clause c → List (Clause c)
applyDeMorgan n (mkAtom name args :- body) = let forAllVars = collectVarsForForAll (mkAtom name args :- body)
  in unfoldr (λ { suc x → not (mkAtom (getNextFreeClauseName n name) ((makeFreeVarArgs forAllVars (length args)) ++ forAllVars)) :-  (reverse ∘ buildNegatedBody (length body - x)) body }) (length body)

buildForAll : {c : 𝒞} → List ℕ → List ℕ → String → Clause c
buildForAll (v ∷ vars) acc name = atomLiteral (mkAtom "forall" (var v ∷ buildForall vars (v ∷ acc) name ∷ []))
buildForAll [] acc name = atomLiteral (not mkAtom name (map var acc))

computeDual : 
  ∀ {Atom 𝒞 Code Constraint}
  → List (ClauseI Atom 𝒞 Code Constraint)
  → List (ClauseI ASPAtom 𝒞 Code Constraint)
computeDual : {c : 𝒞} → List (Clause c) → List (Clause c)
computeDual ((mkAtom name args :- body) ∷ xs) = 
  (not (mkAtom name ((count ∘ length) args)) :- makeTopLevelBody ((suc ∘ length) xs)) ∷
  foldr
    (λ {(suc n , (mkAtom name args :- body)) x → 
      (n , if (_≡ᵇ_ 0 ∘ length ∘ collectVarsForForAll) (mkAtom name args :- body)
           then applyDeMorgan ((suc ∘ length) xs - n) (mkAtom name args :- body)
           else (not (mkAtom name (makeFreeVarArgs (collectVarsForForAll (mkAtom name args :- body)) (length args))) :- 
              buildForAll (collectVarsForForAll (mkAtom name args :- body)) [] (getNextFreeClauseName ((suc ∘ length) xs - n) name))
              ∷ applyDeMorgan ((suc ∘ length) xs - n)) (mkAtom name args :- body ++ map 𝓁Literal (makeParamUnificationExplicit args))} )
           (zero , [])
           ((mkAtom name args :- body) ∷ xs)

cForall₀ : 
  ∀ {𝒞 Code Constraint}
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → Bool
cForall₀ [] _ = nothing
cForall₀ (newConstraints ∷ xs) store with (schedule (store ++ (negate newConstraints)) []) 
... | just _ = cForall₀ xs (store ++ (negate newConstraints))
... | nothing = just []

cForall : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → (zipAtom : AbstractAtom → AbstractAtom → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → Clause ConcreteAtom validate 𝒞 Code Constraint
  → Body ConcreteAtom (validate bodyOfRule) 𝒞 Code Constraint
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → (findAll : Bool)
  → if findAll 
    then (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
    else (Maybe ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
cForall zipAtom zipValue program goal constraints findAll = cForall₀ (eval zipAtom zipValue program goal [] true subst) []

addNmr : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → List (Literal Atom 𝒞 Code Constraint)
  → List (Literal ASPAtom 𝒞 Code Constraint)
addNmr [] = nmrCheck ∷ []
addNmr (x ∷ xs) = wrap x 0 [] ∷ addNmr xs

aspExecute : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → ⦃ DecEq 𝒞 ⦄
  → ⦃ Solver 𝒞 Code Constraint ⦄
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → (zipValue : (c : 𝒞) → Code c → Code c → Maybe (List (Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint)))
  → Clause Atom validate 𝒞 Code Constraint
  → Body Atom (validate bodyOfRule) 𝒞 Code Constraint
  → (findAll : Bool)
  → if findAll 
    then (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
    else (Maybe ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint)) -- type depends on whether findall mode is activated
aspExecute zipValue = 
  clpExecute zipAtom zipValue (computeNmr program ∘ computeDual program) addNmr (((λ { (forAll _ _) → true ; _ → false }) , cForall) ∷ [])