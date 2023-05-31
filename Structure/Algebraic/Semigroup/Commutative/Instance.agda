open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

module Structure.Algebraic.Semigroup.Commutative.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (∙-left-congruent : LeftCongruent _∙_)
    (∙-commute : Commute _∙_)
    (∙-assoc : Associate _∙_)
    where

open import Structure.Algebraic.Magma.Commutative.Instance _∙_ ∙-left-congruent ∙-commute public
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative

instance
    ∙-is-associative : IsAssociative _∙_
    ∙-is-associative = record {associate = ∙-assoc} 

    ∙-semigroup : Semigroup _∙_
    ∙-semigroup = record {}

    ∙-commutative-semigroup : CommutativeSemigroup _∙_
    ∙-commutative-semigroup = record {}