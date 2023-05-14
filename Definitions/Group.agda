module Definitions.Group where

open import Agda.Primitive
open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record Group {ℓA ℓ=A : Level} {A : Set ℓA} (_∙_ : BinOp A) (i : A) (_⁻¹ : A → A) : Set (ℓA ⊔ lsuc ℓ=A) where
    field
        overlap {{base-monoid}} : Monoid {ℓA} {ℓ=A} _∙_ i
        overlap {{has-inverse}} : HasInverse _∙_ i _⁻¹ 