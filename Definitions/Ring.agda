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

record Ring {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_+_ : BinOp A) (_*_ : BinOp A) (0A 1A : A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        {{+-abelian-group}} : AbelianGroup _+_ 0A neg
        {{*-monoid}} : Monoid _*_ 1A
        {{ringoid}} : Ringoid _+_ _*_

    open Setoid {{...}}
    open AbelianGroup {{...}}
    open Group {{...}}
    open BiInjective {{...}}
    open Ringoid {{...}}
 
    private
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

        semiring : Semiring _+_ _*_
        semiring = record {}