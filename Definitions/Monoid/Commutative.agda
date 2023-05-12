module Definitions.Monoid.Commutative where

open import Agda.Primitive
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record CommutativeMonoid {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) (i : S) : Set (lsuc ℓ) where
    field
        {{commutative-semigroup}} : CommutativeSemigroup _∙_
        overlap {{base-monoid}} : Monoid _∙_ i