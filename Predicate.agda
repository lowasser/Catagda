module Predicate where

open import Agda.Primitive

Predicate : {ℓA : Level} → (ℓP : Level) → Set ℓA → Set (ℓA ⊔ lsuc ℓP)
Predicate ℓP A = A → Set ℓP