module Data.Pair where

open import Agda.Primitive 
open import Agda.Builtin.Sigma

_×_ : {ℓA ℓB : Level} → (A : Set ℓA) → (B : Set ℓB) → Set (ℓA ⊔ ℓB)
A × B = Σ A (λ _ → B)