module Definitions.Relation.Order.Total where

open import Agda.Primitive
open import Definitions.Either
open import Definitions.Setoid
open import Definitions.Relation
open import Definitions.Relation.Order.Partial

open Setoid {{...}}

record TotalOrder {ℓA ℓ=A ℓ≤A : Level} {A : Set ℓA} {{AS : Setoid ℓ=A A}} (_≤_ : Rel ℓ≤A A) : Set (ℓA ⊔ ℓ=A ⊔ ℓ≤A) where
    field
        {{is-partial-order}} : PartialOrder _≤_
        compare : (a b : A) → Either (a ≤ b) (b ≤ a)

open TotalOrder {{...}}

compare-order-on : {ℓA ℓ=A ℓ≤A : Level} {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{TO : TotalOrder _≤_}} → (a b : A) → Either (a ≤ b) (b ≤ a)
compare-order-on _ = compare