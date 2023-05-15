module Definitions.Group.Abelian where

open import Agda.Primitive
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record AbelianGroup {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) (i : S) (_⁻¹ : S → S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        {{commutative-monoid}} : CommutativeMonoid {ℓS} {ℓ=S} _∙_ i
        overlap {{base-group}} : Group {ℓS} {ℓ=S} _∙_ i _⁻¹