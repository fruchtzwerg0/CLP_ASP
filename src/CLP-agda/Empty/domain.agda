module Empty.domain where

open import Data.Empty
open import CLP.ftUtilsDerivation

instance  ftUtils⊥ : FTUtils ⊥
          ftUtils⊥ .functor = ⊥-elim
          ftUtils⊥ .getNat = ⊥-elim
          ftUtils⊥ .varName = ⊥-elim
          ftUtils⊥ .occurs _ = ⊥-elim
          ftUtils⊥ .collectVars = ⊥-elim