module Definitions.Monoid.Commutative where

open import Agda.Primitive
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Setoid

record CommutativeMonoid {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) (i : S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        {{commutative-semigroup}} : CommutativeSemigroup _∙_
        overlap {{base-monoid}} : Monoid _∙_ i