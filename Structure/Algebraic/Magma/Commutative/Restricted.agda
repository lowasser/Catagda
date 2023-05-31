open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid
open import Structure.Algebraic.Magma.Commutative

module Structure.Algebraic.Magma.Commutative.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    {{M∙ : CommutativeMagma _∙_}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    where

open import Structure.Restricted
open CommutativeMagma {{...}}

open import Structure.Algebraic.Magma.Restricted _∙_ P combine public

private 
    commute : Commute restricted-op
    commute (a constraint pa) (b constraint pb) = eq-restricted (commute-on _∙_ a b)

instance
    restricted-op-is-commutative : IsCommutative restricted-op
    restricted-op-is-commutative = record { commute = commute }

    restricted-op-commutative-magma : CommutativeMagma restricted-op
    restricted-op-commutative-magma = record {}