module Definitions.Relation.Order.Pre where

open import Agda.Primitive
open import Definitions.Relation
open import Definitions.Relation.Properties

record PreOrder {ℓ : Level} {A : Set ℓ} (_~_ : Relation A) : Set ℓ where
    field
        {{is-reflexive}} : IsReflexive _~_
        {{is-transitive}} : IsTransitive _~_