module Structure.Algebraic.Ring.Commutative where

open import Agda.Primitive
open import Structure.Setoid
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Group
open import Structure.Algebraic.Group.Abelian
open import Function.Binary
open import Structure.Algebraic.Ring

private
    variable
        ℓA ℓ=A : Level

record CommutativeRing {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        overlap {{underlying-ring}} : Ring _*_ _+_ 1A 0A neg
        overlap {{*-commutative-monoid}} : CommutativeMonoid {ℓA} {ℓ=A} _*_ 1A