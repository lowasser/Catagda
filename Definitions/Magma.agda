module Definitions.Magma where

open import Agda.Primitive
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Properties

record Magma {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) : Set (lsuc ℓ) where
    field
        {{magma-setoid}} : Setoid S
        {{magma-bi-congruent}} : BiCongruent _∙_
 