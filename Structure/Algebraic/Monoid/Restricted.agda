open import Agda.Primitive
open import Function.Binary
open import Structure.Setoid
open import Structure.Algebraic.Monoid

module Structure.Algebraic.Monoid.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    {{M∙ : Monoid _∙_ i}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    (pi : P i)
    where

open import Structure.Restricted
open import Structure.Setoid.Restricted A P
open Monoid {{...}}

open import Function.Binary.Properties
open import Structure.Algebraic.Semigroup.Restricted _∙_ P combine public

restricted-identity : A RestrictedTo P
restricted-identity = i constraint pi

private
    left-identity : LeftIdentity restricted-op restricted-identity
    left-identity (a constraint _) = eq-restricted (left-identity-on _∙_ a)

    right-identity : RightIdentity restricted-op restricted-identity
    right-identity (a constraint _) = eq-restricted (right-identity-on _∙_ a)

instance
    restricted-has-identity : HasIdentity restricted-op restricted-identity
    restricted-has-identity = record {left-identity = left-identity; right-identity = right-identity}

    restricted-monoid : Monoid restricted-op restricted-identity
    restricted-monoid = record {}