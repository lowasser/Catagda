module Definitions.Group.Abelian where

open import Agda.Primitive
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid

record AbelianGroup {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) (i : S) (_⁻¹ : S → S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-group}} : Group _∙_ i _⁻¹
        overlap {{commutative-monoid}} : CommutativeMonoid _∙_ i