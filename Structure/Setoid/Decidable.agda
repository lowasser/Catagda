module Structure.Setoid.Decidable where

open import Agda.Primitive
open import Data.Either
open import Structure.Setoid
open import Relation.Properties
open import Definitions.Not

open Setoid {{...}}

record DecidableSetoid {ℓA : Level} (ℓ= : Level) (A : Set ℓA) : Set (ℓA ⊔ lsuc ℓ=) where
    field
        {{setoid}} : Setoid ℓ= A
        {{decidable}} : Decidable _≅_

make-decidable-setoid : {ℓA ℓ= : Level} {A : Set ℓA} → {{SA : Setoid ℓ= A}} → ((a b : A) → Either (a ≅ b) (¬ (a ≅ b))) → DecidableSetoid ℓ= A
make-decidable-setoid decide = record {decidable = record {decide = decide}}