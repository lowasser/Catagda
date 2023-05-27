module Definitions.Field where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Group.Abelian
open import Definitions.Function.Binary
open import Definitions.Ring
open import Definitions.Ring.Commutative
open import Definitions.Logic
open import Definitions.Function.Binary.Properties

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