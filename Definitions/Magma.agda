module Definitions.Magma where

open import Agda.Primitive
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid
open import Definitions.Relation.Properties

record Magma {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        {{magma-setoid}} : Setoid ℓ=S S
        {{magma-bi-congruent}} : BiCongruent _∙_

make-magma : {ℓS ℓ=S : Level} {S : Set ℓS} → {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → LeftCongruent _∙_ → RightCongruent _∙_ → Magma _∙_
make-magma _ lc rc = record { magma-bi-congruent = record {left-congruent = lc; right-congruent = rc}}