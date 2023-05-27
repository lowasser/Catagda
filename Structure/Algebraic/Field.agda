module Structure.Algebraic.Field where

open import Agda.Primitive
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Group
open import Structure.Algebraic.Group.Abelian
open import Function.Binary
open import Structure.Algebraic.Ring
open import Structure.Algebraic.Ring.Commutative
open import Logic
open import Function.Binary.Properties

open Setoid {{...}}

private
    variable
        ℓA ℓ=A : Level

record Field {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (minv : (x : A) → ¬ (x ≅ 0A) → A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        overlap {{commutative-ring}} : CommutativeRing _*_ _+_ 1A 0A neg
        left-multiplicative-inverse : (x : A) → (x≠0 : ¬ (x ≅ 0A)) → minv x x≠0 * x ≅ 1A

    right-multiplicative-inverse : (x : A) → (x≠0 : ¬ (x ≅ 0A)) → x * minv x x≠0 ≅ 1A
    right-multiplicative-inverse x x≠0 = begin≅
        x * minv x x≠0      ≅< commute-on _*_ x (minv x x≠0) >
        minv x x≠0 * x      ≅< left-multiplicative-inverse x x≠0 >
        1A                  ∎