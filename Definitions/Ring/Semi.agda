module Definitions.Ring.Semi where

open import Agda.Primitive
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative 
open import Definitions.Ringoid
open import Definitions.Function.Binary
open import Definitions.Setoid

record Semiring {ℓA ℓ=A : Level} {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_+_ _*_ : BinOp A) : Set (ℓA ⊔ lsuc ℓ=A) where
    field
        {{+-commutative-semigroup}} : CommutativeSemigroup _+_
        {{*-semigroup}} : Semigroup _*_
        {{ringoid}} : Ringoid _+_ _*_