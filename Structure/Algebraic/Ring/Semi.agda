module Structure.Algebraic.Ring.Semi where

open import Agda.Primitive
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative 
open import Structure.Algebraic.Ringoid
open import Function.Binary
open import Structure.Setoid

record Semiring {ℓA ℓ=A : Level} {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ _+_ : BinOp A) : Set (ℓA ⊔ lsuc ℓ=A) where
    field
        {{+-commutative-semigroup}} : CommutativeSemigroup _+_
        {{*-semigroup}} : Semigroup _*_
        {{ringoid}} : Ringoid _*_ _+_