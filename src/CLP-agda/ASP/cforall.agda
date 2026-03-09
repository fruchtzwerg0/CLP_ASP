cForall₀ : 
  ∀ {𝒞 Code Constraint}
  → ⦃ Scheduler 𝒞 Code Constraint ⦄
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → Bool
cForall₀ [] _ = nothing
cForall₀ (newConstraints ∷ xs) store with (any (is-just ∘ schedule ∘ _++_ store ∘ negateLiteral ∘ constraint)) newConstraints
... | true = cForall₀ xs (store ++ (negate newConstraints))
... | false = just []

cForall : 
  ∀ {Atom 𝒞 validate Code Constraint}
  → Clause ConcreteAtom validate 𝒞 Code Constraint
  → Body ConcreteAtom (validate bodyOfRule) 𝒞 Code Constraint
  → List ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
  → (findAll : Bool)
  → if findAll 
    then (List ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
    else (Maybe ∘ List) ((Σᵢ 𝒞 (ℒ ∘ Code) Code Constraint) ⊎ (Σᵢ 𝒞 (Dual ∘ Constraint) Code Constraint))
cForall program goal constraints findAll = cForall₀ (eval program goal [] true subst) []