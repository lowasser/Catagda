module Structure.Algebraic.Magma where

open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid
open import Relation.Properties

record Magma {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{magma-bi-congruent}} : BiCongruent _∙_

make-magma : {ℓS ℓ=S : Level} {S : Set ℓS} → {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → LeftCongruent _∙_ → RightCongruent _∙_ → Magma _∙_
make-magma _ lc rc = record { magma-bi-congruent = record {left-congruent = lc; right-congruent = rc}}