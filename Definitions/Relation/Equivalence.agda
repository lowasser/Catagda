module Definitions.Relation.Equivalence where

open import Agda.Primitive
open import Definitions.Relation
open import Definitions.Relation.Properties

record Equivalence { ℓ : Level } { A : Set ℓ} (_∼_ : Relation A) : Set ℓ where
    field
        {{is-symmetric}} : IsSymmetric _∼_
        {{is-transitive}} : IsTransitive _∼_
        {{is-reflexive}} : IsReflexive _∼_
