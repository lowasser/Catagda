module Definitions.Ring.Commutative where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Group.Abelian
open import Definitions.Function.Binary
open import Definitions.Ring

private
    variable
        ℓA ℓ=A : Level

record CommutativeRing {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_+_ : BinOp A) (_*_ : BinOp A) (0A 1A : A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        {{underlying-ring}} : Ring _+_ _*_ 0A 1A neg
        {{*-commutative-monoid}} : CommutativeMonoid {ℓA} {ℓ=A} _*_ 1A