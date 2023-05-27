module Definitions.Ring where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Semigroup
open import Definitions.Magma
open import Definitions.Group
open import Definitions.Group.Abelian
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Relation
open import Definitions.Ringoid
open import Definitions.Ring.Semi

private
    variable
        ℓA ℓ=A : Level

record Ring {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ _+_ : BinOp A) (1A 0A : A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        overlap {{+-abelian-group}} : AbelianGroup _+_ 0A neg
        overlap {{*-monoid}} : Monoid _*_ 1A
        overlap {{ringoid}} : Ringoid _*_ _+_

    open Setoid {{...}}
    open AbelianGroup {{...}}
    open Group {{...}}
    open BiInjective {{...}}
    open Ringoid {{...}}
    
    left-zero : LeftZero _*_ 0A
    left-zero a = left-injective (0A * a) (begin≅
        (0A * a) + (0A * a)         ≅< symmetric-on A (right-distribute 0A 0A a) >
        (0A + 0A) * a               ≅< right-congruent-on _*_ (left-id-on _+_ 0A) >
        0A * a                      ≅< symmetric-on A (right-id-on _+_ (0A * a)) >
        (0A * a) + 0A               ∎)
    
    right-zero : RightZero _*_ 0A
    right-zero a = left-injective (a * 0A) (begin≅
        (a * 0A) + (a * 0A)         ≅< symmetric-on A (left-distribute a 0A 0A) >
        a * (0A + 0A)               ≅< left-congruent-on _*_ (left-id-on _+_ 0A) >
        a * 0A                      ≅< symmetric-on A (right-id-on _+_ (a * 0A)) >
        (a * 0A) + 0A               ∎)

    instance
        zero : HasZero _*_ 0A
        zero = record {left-zero = left-zero; right-zero = right-zero}

        semiring : Semiring _*_ _+_
        semiring = record {}

open Ring {{...}}
open Setoid {{...}}

right-times-neg-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_*_ _+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{R : Ring _*_ _+_ 1A 0A neg}} →
    (a b : A) → a * neg b ≅ neg (a * b)
right-times-neg-on {_} {_} {A} _*_ _+_ 1A 0A neg a b = right-inverse-is-unique-on _+_ 0A neg (a * b) (a * neg b) (begin≅
    (a * b) + (a * neg b)           ≅< symmetric-on A (left-distribute-on _*_ _+_ a b (neg b)) >
    a * (b + neg b)                 ≅< left-congruent-on _*_ (right-inverse-on _+_ 0A neg b) >
    a * 0A                          ≅< right-zero a >
    0A                              ∎)

left-times-neg-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_*_ _+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{R : Ring _*_ _+_ 1A 0A neg}} →
    (a b : A) → neg a * b ≅ neg (a * b)
left-times-neg-on {_} {_} {A} _*_ _+_ 1A 0A neg a b = right-inverse-is-unique-on _+_ 0A neg (a * b) (neg a * b) (begin≅
    (a * b) + (neg a * b)           ≅< symmetric-on A (right-distribute-on _*_ _+_ a (neg a) b) >
    (a + neg a) * b                 ≅< right-congruent-on _*_ (right-inverse-on _+_ 0A neg a) >
    0A * b                          ≅< left-zero b >
    0A                              ∎)

commute-times-neg-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_*_ _+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{R : Ring _*_ _+_ 1A 0A neg}} →
    (a b : A) → neg a * b ≅ a * neg b
commute-times-neg-on {_} {_} {A} _*_ _+_ 1A 0A neg a b = begin≅
    neg a * b               ≅< left-times-neg-on _*_ _+_ 1A 0A neg a b >
    neg (a * b)             ≅< symmetric-on A (right-times-neg-on _*_ _+_ 1A 0A neg a b) >
    a * neg b               ∎