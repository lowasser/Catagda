module Definitions.Relation.Order.Total where

open import Agda.Primitive
open import Definitions.Either
open import Definitions.Setoid
open import Definitions.Relation
open import Definitions.Relation.Order.Partial

open Setoid {{...}}

record TotalOrder {ℓ : Level} {A : Set ℓ} {{AS : Setoid A}} (_≤_ : Relation A) : Set ℓ where
    field
        {{is-partial-order}} : PartialOrder _≤_
        compare : (a b : A) → Either (a ≤ b) (b ≤ a)

open TotalOrder {{...}}

compare-order-on : {ℓ : Level} {A : Set ℓ} → {{AS : Setoid A}} → (_≤_ : Relation A) → {{TO : TotalOrder _≤_}} → (a b : A) → Either (a ≤ b) (b ≤ a)
compare-order-on _ = compare