module Definitions.Monoid.Commutative where

open import Agda.Primitive
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record CommutativeMonoid {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) (i : S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        {{commutative-semigroup}} : CommutativeSemigroup {ℓS} {ℓ=S} _∙_
        overlap {{base-monoid}} : Monoid {ℓS} {ℓ=S} _∙_ i