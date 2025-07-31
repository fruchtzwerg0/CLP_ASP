module Term.types where

open import Data.String 
  using (String)
open import Data.List 
  using (List)

-- The term datatype (prolog)
-- NO_POSITIVITY_CHECK is mandatory because the extension f (Term f) is not positive.
{-# NO_POSITIVITY_CHECK #-}
data Term (f : Set → Set) : Set where
  atomT : String → List (f (Term f)) → Term f