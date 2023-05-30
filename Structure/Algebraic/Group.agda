module Structure.Algebraic.Group where

open import Agda.Primitive
open import Structure.Algebraic.Monoid
open import Function.Binary
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Magma

open Monoid {{...}}
open Semigroup {{...}}
open Magma {{...}}
open Setoid {{...}}

record Group {ℓA ℓ=A : Level} {A : Set ℓA} {{SA : Setoid ℓ=A A}}  (_∙_ : BinOp A) (i : A) (_⁻¹ : A → A) : Set (ℓA ⊔ lsuc ℓ=A) where
    field
        overlap {{base-monoid}} : Monoid {{SA}} _∙_ i
        overlap {{has-inverse}} : HasInverse _∙_ i _⁻¹

    left-inverse-is-unique : (x xi : A) → (xi ∙ x ≅ i) → xi ≅ x ⁻¹
    left-inverse-is-unique x xi xix=i = begin≅
        xi                  ≅< symmetric-on A (right-id-on _∙_ xi) >
        xi ∙ i              ≅< left-congruent-on _∙_ (symmetric-on A (right-inverse-on _∙_ i _⁻¹ x)) >
        xi ∙ (x ∙ (x ⁻¹))   ≅< left-associate-on _∙_ xi x (x ⁻¹) >
        (xi ∙ x) ∙ (x ⁻¹)   ≅< right-congruent-on _∙_ xix=i >
        i ∙ (x ⁻¹)          ≅< left-id-on _∙_ (x ⁻¹) >
        x ⁻¹                ∎
    
    right-inverse-is-unique : (x xi : A) → (x ∙ xi ≅ i) → xi ≅ x ⁻¹
    right-inverse-is-unique x xi xxi=i = begin≅
        xi                  ≅< symmetric-on A (left-id-on _∙_ xi) >
        i ∙ xi              ≅< right-congruent-on _∙_ (symmetric-on A (left-inverse-on _∙_ i _⁻¹ x)) >
        ((x ⁻¹) ∙ x) ∙ xi   ≅< right-associate-on _∙_ (x ⁻¹) x xi >
        (x ⁻¹) ∙ (x ∙ xi)   ≅< left-congruent-on _∙_ xxi=i >
        (x ⁻¹) ∙ i          ≅< right-id-on _∙_ (x ⁻¹) >
        x ⁻¹                ∎

    inverse-inverse : (x : A) → (x ⁻¹) ⁻¹ ≅ x
    inverse-inverse x = symmetric-on A (left-inverse-is-unique (x ⁻¹) x (right-inverse-on _∙_ i _⁻¹ x))

    distribute-inverse : (a b : A) → (a ∙ b) ⁻¹ ≅ (b ⁻¹) ∙ (a ⁻¹)
    distribute-inverse a b = symmetric-on A (left-inverse-is-unique (a ∙ b) ((b ⁻¹) ∙ (a ⁻¹)) (begin≅
        ((b ⁻¹) ∙ (a ⁻¹)) ∙ (a ∙ b)                 ≅< left-associate-on _∙_ ((b ⁻¹) ∙ (a ⁻¹)) a b >
        (((b ⁻¹) ∙ (a ⁻¹)) ∙ a) ∙ b                 ≅< right-congruent-on _∙_ (right-associate-on _∙_ (b ⁻¹) (a ⁻¹) a) >
        ((b ⁻¹) ∙ ((a ⁻¹) ∙ a)) ∙ b                 ≅< right-congruent-on _∙_ (left-congruent-on _∙_ (left-inverse-on _∙_ i _⁻¹ a)) >
        ((b ⁻¹) ∙ i) ∙ b                            ≅< right-congruent-on _∙_ (right-id-on _∙_ (b ⁻¹)) >
        (b ⁻¹) ∙ b                                  ≅< left-inverse-on _∙_ i _⁻¹ b >
        i                                           ∎))

    private
        left-injective : (a : A) → Injective (a ∙_)
        left-injective a {b} {c} ab=ac = begin≅
            b                   ≅< symmetric-on A (left-id-on _∙_ b) >
            i ∙ b               ≅< right-congruent-on _∙_ (symmetric-on A (left-inverse-on _∙_ i _⁻¹ a)) >
            ((a ⁻¹) ∙ a) ∙ b    ≅< right-associate-on _∙_ (a ⁻¹) a b >
            (a ⁻¹) ∙ (a ∙ b)    ≅< left-congruent-on _∙_ ab=ac >
            (a ⁻¹) ∙ (a ∙ c)    ≅< left-associate-on _∙_ (a ⁻¹) a c >
            ((a ⁻¹) ∙ a) ∙ c    ≅< right-congruent-on _∙_ (left-inverse-on _∙_ i _⁻¹ a) >
            i ∙ c               ≅< left-id-on _∙_ c >
            c                   ∎

        right-injective : (c : A) → Injective (_∙ c)
        right-injective c {a} {b} ac=bc = begin≅
            a                   ≅< symmetric-on A (right-id-on _∙_ a) >
            a ∙ i               ≅< left-congruent-on _∙_ (symmetric-on A (right-inverse-on _∙_ i _⁻¹ c)) >
            a ∙ (c ∙ (c ⁻¹))    ≅< left-associate-on _∙_ a c (c ⁻¹) >
            (a ∙ c) ∙ (c ⁻¹)    ≅< right-congruent-on _∙_ ac=bc >
            (b ∙ c) ∙ (c ⁻¹)    ≅< right-associate-on _∙_ b c (c ⁻¹) >
            b ∙ (c ∙ (c ⁻¹))    ≅< left-congruent-on _∙_ (right-inverse-on _∙_ i _⁻¹ c) >
            b ∙ i               ≅< right-id-on _∙_ b >
            b                   ∎
    
    instance
        bi-injective : BiInjective _∙_
        bi-injective = record {left-injective = left-injective; right-injective = right-injective}

open Group {{...}}

right-inverse-is-unique-on : {ℓA ℓ=A : Level} {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (i : A) → (_⁻¹ : A → A) → {{G : Group _∙_ i _⁻¹}} → (x xi : A) → (x ∙ xi ≅ i) → xi ≅ x ⁻¹
right-inverse-is-unique-on _ _ _ = right-inverse-is-unique

distribute-inverse-on : {ℓA ℓ=A : Level} {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (i : A) → (_⁻¹ : A → A) → {{G : Group _∙_ i _⁻¹}} → (a b : A) → ((a ∙ b) ⁻¹) ≅ (b ⁻¹) ∙ (a ⁻¹)
distribute-inverse-on _ _ _ = distribute-inverse

inverse-inverse-on : {ℓA ℓ=A : Level} {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (i : A) → (_⁻¹ : A → A) → {{G : Group _∙_ i _⁻¹}} → (a : A) → (a ⁻¹) ⁻¹ ≅ a
inverse-inverse-on _ _ _ = inverse-inverse