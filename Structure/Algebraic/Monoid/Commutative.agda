module Structure.Algebraic.Monoid.Commutative where

open import Agda.Primitive
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Monoid
open import Function.Binary
open import Structure.Setoid

record CommutativeMonoid {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) (i : S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{commutative-semigroup}} : CommutativeSemigroup _∙_
        overlap {{base-monoid}} : Monoid _∙_ i