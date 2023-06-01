open import Agda.Primitive
open import Function.Binary
open import Structure.Setoid
open import Structure.Algebraic.Semigroup.Commutative

module Structure.Algebraic.Semigroup.Commutative.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    {{CSG∙ : CommutativeSemigroup _∙_}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    where

open import Structure.Restricted
open import Structure.Setoid.Restricted A P
open CommutativeSemigroup {{...}}

open import Function.Binary.Properties
open import Structure.Algebraic.Semigroup.Restricted _∙_ P combine public
open import Structure.Algebraic.Magma.Commutative

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