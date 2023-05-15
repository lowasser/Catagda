module Definitions.Ring where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Group.Abelian
open import Definitions.Function.Binary

private
    variable
        ℓA ℓ=A : Level

record Ring {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_+_ : BinOp A) (_*_ : BinOp A) (0A 1A : A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        {{+-abelian-group}} : AbelianGroup {ℓA} {ℓ=A} _+_ 0A neg
        {{*-monoid}} : Monoid {ℓA} {ℓ=A} _*_ 1A
        distribute : ∀ (a b c : A) → Setoid._≅_ SA (a * (b + c)) ((a * b) + (a * c))