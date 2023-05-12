module Definitions.Either where

open import Agda.Primitive

data Either {ℓA ℓB : Level} (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
    left : A → Either A B
    right : B → Either A B