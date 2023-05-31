open import Agda.Primitive
open import Function.Binary
open import Structure.Setoid
open import Structure.Algebraic.Monoid.Commutative

module Structure.Algebraic.Monoid.Commutative.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    {{CSG∙ : CommutativeMonoid _∙_ i}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    (pi : P i)
    where

open import Structure.Restricted
open CommutativeMonoid {{...}}

open import Function.Binary.Properties
open import Structure.Algebraic.Monoid.Restricted _∙_ i P combine pi public
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup.Commutative

private 
    commute : Commute restricted-op
    commute (a constraint pa) (b constraint pb) = eq-restricted (commute-on _∙_ a b)

instance
    restricted-op-is-commutative : IsCommutative restricted-op
    restricted-op-is-commutative = record {commute = commute}

    restricted-op-commutative-magma : CommutativeMagma restricted-op
    restricted-op-commutative-magma = record {}

    restricted-commutative-semigroup : CommutativeSemigroup restricted-op
    restricted-commutative-semigroup = record {}

    restricted-commutative-monoid : CommutativeMonoid restricted-op restricted-identity
    restricted-commutative-monoid = record {}