open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

module Structure.Algebraic.Monoid.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    {{∙-bi-congruent : BiCongruent _∙_}}
    (∙-assoc : Associate _∙_)
    (∙-left-identity : LeftIdentity _∙_ i)
    (∙-right-identity : RightIdentity _∙_ i)
    where

open import Structure.Algebraic.Semigroup.Instance _∙_ ∙-assoc public

open import Structure.Algebraic.Monoid

instance
    ∙-has-identity : HasIdentity _∙_ i
    ∙-has-identity = record {left-identity = ∙-left-identity; right-identity = ∙-right-identity}

    ∙-monoid : Monoid _∙_ i
    ∙-monoid = record {}