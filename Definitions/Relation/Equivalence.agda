module Definitions.Relation.Equivalence where

open import Agda.Primitive
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Order.Pre

record Equivalence { ℓ : Level } { A : Set ℓ} (_∼_ : Relation A) : Set ℓ where
    field
        {{is-preorder}} : PreOrder _∼_
        {{is-symmetric}} : IsSymmetric _∼_
