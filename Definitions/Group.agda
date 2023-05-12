module Definitions.Group where

open import Agda.Primitive
open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record Group {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) (i : S) (_⁻¹ : S → S) : Set (lsuc ℓ) where
    field
        overlap {{base-monoid}} : Monoid _∙_ i
        overlap {{has-inverse}} : HasInverse _∙_ i _⁻¹