module Definitions.Semigroup.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid
open import Definitions.Setoid.Equation

private
    variable
        ℓS ℓ=S : Level


record CommutativeSemigroup {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{commutative-magma}} : CommutativeMagma _∙_
        overlap {{base-semigroup}} : Semigroup _∙_

    open Semigroup {{...}}
    open IsAssociative {{...}}
    open CommutativeMagma {{...}}
    open IsCommutative {{...}}
    open Setoid {{...}}
    open Magma {{...}}
    
    <ab><cd>-to-<ad><cb> : (a b c d : S) → ((a ∙ b) ∙ (c ∙ d)) ≅ ((a ∙ d) ∙ (c ∙ b))
    <ab><cd>-to-<ad><cb> a b c d = begin≅
        (a ∙ b) ∙ (c ∙ d)       ≅< left-associate-on _∙_ (a ∙ b) c d >
        ((a ∙ b) ∙ c) ∙ d       ≅< commute-on _∙_ ((a ∙ b) ∙ c) d >
        d ∙ ((a ∙ b) ∙ c)       ≅< left-congruent-on _∙_ (right-associate-on _∙_ a b c) >
        d ∙ (a ∙ (b ∙ c))       ≅< left-associate-on _∙_ d a (b ∙ c) >
        (d ∙ a) ∙ (b ∙ c)       ≅< bi-congruent _∙_ (commute-on _∙_ d a) (commute-on _∙_ b c) >
        (a ∙ d) ∙ (c ∙ b)       ∎