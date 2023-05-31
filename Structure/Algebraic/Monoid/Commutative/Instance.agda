open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

module Structure.Algebraic.Monoid.Commutative.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    (∙-left-congruent : LeftCongruent _∙_)
    (∙-commute : Commute _∙_)
    (∙-assoc : Associate _∙_)
    (∙-left-identity : LeftIdentity _∙_ i)
    where

open import Structure.Algebraic.Semigroup.Commutative.Instance _∙_ ∙-left-congruent ∙-commute ∙-assoc public
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Monoid.Commutative

instance
    ∙-has-identity : HasIdentity _∙_ i
    ∙-has-identity = has-identity-commute ∙-left-identity

    ∙-monoid : Monoid _∙_ i
    ∙-monoid = record {}

    ∙-commutative-monoid : CommutativeMonoid _∙_ i
    ∙-commutative-monoid = record {}