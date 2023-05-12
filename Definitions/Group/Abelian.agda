module Definitions.Group.Abelian where

open import Agda.Primitive
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record AbelianGroup {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) (i : S) (_⁻¹ : S → S) : Set (lsuc ℓ) where
    field
        {{commutative-monoid}} : CommutativeMonoid _∙_ i
        overlap {{base-group}} : Group _∙_ i _⁻¹