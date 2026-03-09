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
  clpExecute zipAtom zipValue (computeNMR program ∘ computeDual program) addNMR (((λ { (forAll _ _) → true ; _ → false }) , cForall) ∷ [])