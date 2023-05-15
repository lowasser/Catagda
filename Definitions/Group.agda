module Definitions.Group where

open import Agda.Primitive
open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Semigroup
open import Definitions.Magma

open Monoid {{...}}
open Semigroup {{...}}
open Magma {{...}}
open Setoid {{...}}

record Group {ℓA ℓ=A : Level} {A : Set ℓA} (_∙_ : BinOp A) (i : A) (_⁻¹ : A → A) : Set (ℓA ⊔ lsuc ℓ=A) where
    field
        overlap {{base-monoid}} : Monoid {ℓA} {ℓ=A} _∙_ i
        overlap {{has-inverse}} : HasInverse _∙_ i _⁻¹
    

    left-inverse-is-unique : (x xi : A) → (xi ∙ x ≅ i) → xi ≅ x ⁻¹
    left-inverse-is-unique x xi xix=i = begin≅
        xi                  ≅< symmetric-on A (right-id-on _∙_ xi) >
        xi ∙ i              ≅< left-congruent-on _∙_ (symmetric-on A (right-inverse-on _∙_ i _⁻¹ x)) >
        xi ∙ (x ∙ (x ⁻¹))   ≅< associate-on _∙_ xi x (x ⁻¹) >
        (xi ∙ x) ∙ (x ⁻¹)   ≅< right-congruent-on _∙_ xix=i >
        i ∙ (x ⁻¹)          ≅< left-id-on _∙_ (x ⁻¹) >
        x ⁻¹                ∎
    
    right-inverse-is-unique : (x xi : A) → (x ∙ xi ≅ i) → xi ≅ x ⁻¹
    right-inverse-is-unique x xi xxi=i = begin≅
        xi                  ≅< symmetric-on A (left-id-on _∙_ xi) >
        i ∙ xi              ≅< right-congruent-on _∙_ (symmetric-on A (left-inverse-on _∙_ i _⁻¹ x)) >
        ((x ⁻¹) ∙ x) ∙ xi   ≅< symmetric-on A (associate-on _∙_ (x ⁻¹) x xi) >
        (x ⁻¹) ∙ (x ∙ xi)   ≅< left-congruent-on _∙_ xxi=i >
        (x ⁻¹) ∙ i          ≅< right-id-on _∙_ (x ⁻¹) >
        x ⁻¹                ∎

    inverse-inverse : (x : A) → (x ⁻¹) ⁻¹ ≅ x
    inverse-inverse x = symmetric-on A (left-inverse-is-unique (x ⁻¹) x (right-inverse-on _∙_ i _⁻¹ x))

    distribute-inverse : (a b : A) → (a ∙ b) ⁻¹ ≅ (b ⁻¹) ∙ (a ⁻¹)
    distribute-inverse a b = symmetric-on A (left-inverse-is-unique (a ∙ b) ((b ⁻¹) ∙ (a ⁻¹)) (begin≅
        ((b ⁻¹) ∙ (a ⁻¹)) ∙ (a ∙ b)                 ≅< associate-on _∙_ ((b ⁻¹) ∙ (a ⁻¹)) a b >
        (((b ⁻¹) ∙ (a ⁻¹)) ∙ a) ∙ b                 ≅< right-congruent-on _∙_ (symmetric-on A (associate-on _∙_ (b ⁻¹) (a ⁻¹) a)) >
        ((b ⁻¹) ∙ ((a ⁻¹) ∙ a)) ∙ b                 ≅< right-congruent-on _∙_ (left-congruent-on _∙_ (left-inverse-on _∙_ i _⁻¹ a)) >
        ((b ⁻¹) ∙ i) ∙ b                            ≅< right-congruent-on _∙_ (right-id-on _∙_ (b ⁻¹)) >
        (b ⁻¹) ∙ b                                  ≅< left-inverse-on _∙_ i _⁻¹ b >
        i                                           ∎))

open Group {{...}}

distribute-inverse-on : {ℓA ℓ=A : Level} {A : Set ℓA} → (_∙_ : BinOp A) → (i : A) → (_⁻¹ : A → A) → {{G : Group {ℓA} {ℓ=A} _∙_ i _⁻¹}} → (a b : A) → ((a ∙ b) ⁻¹) ≅ (b ⁻¹) ∙ (a ⁻¹)
distribute-inverse-on _ _ _ = distribute-inverse