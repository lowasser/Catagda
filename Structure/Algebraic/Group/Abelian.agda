module Structure.Algebraic.Group.Abelian where

open import Agda.Primitive
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Group
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

record AbelianGroup {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) (i : S) (_⁻¹ : S → S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-group}} : Group _∙_ i _⁻¹
        overlap {{commutative-monoid}} : CommutativeMonoid _∙_ i