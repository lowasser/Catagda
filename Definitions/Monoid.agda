module Definitions.Monoid where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record Monoid {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) (i : S) : Set (lsuc ℓ) where
    field
        overlap {{base-semigroup}} : Semigroup _∙_
        overlap {{has-identity}} : HasIdentity _∙_ i