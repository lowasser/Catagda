module Structure.Algebraic.Magma.Commutative where

open import Agda.Primitive
open import Structure.Algebraic.Magma
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

record CommutativeMagma {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-magma}} : Magma _∙_
        {{is-commutative}} : IsCommutative _∙_