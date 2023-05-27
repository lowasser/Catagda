module Structure.Algebraic.IntegralDomain where

open import Agda.Primitive
open import Structure.Algebraic.Ring.Commutative
open import Structure.Setoid
open import Function.Binary
open import Data.Either
open import Logic
open import Structure.Setoid.Equation
open import Structure.Algebraic.Ringoid
open import Function.Binary.Properties
open import Structure.Algebraic.Ring
open import Structure.Algebraic.Group.Abelian
open import Structure.Algebraic.Group
open import Structure.Algebraic.Monoid

private
    variable
        ℓA ℓ=A : Level

open Setoid {{...}}

record IntegralDomain {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (neg : A → A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        overlap {{commutative-ring}} : CommutativeRing _*_ _+_ 1A 0A neg
        product-is-zero-one-is-zero : (a b : A) → (a * b) ≅ 0A → Either (a ≅ 0A) (b ≅ 0A)

open IntegralDomain {{...}}

product-is-zero-one-is-zero-on : {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{ID : IntegralDomain _*_ _+_ 1A 0A neg}} →
        (a b : A) → a * b ≅ 0A → Either (a ≅ 0A) (b ≅ 0A)
product-is-zero-one-is-zero-on _ _ _ _ _ = product-is-zero-one-is-zero

private
    cancel-left-multiplication-by-nonzero-helper : {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{ID : IntegralDomain _*_ _+_ 1A 0A neg}} →
        (a b c : A) → a * b ≅ a * c → Either (a ≅ 0A) (b + neg c ≅ 0A)
    cancel-left-multiplication-by-nonzero-helper {_} {_} {A} _*_ _+_ 1A 0A neg a b c ab=ac = product-is-zero-one-is-zero a (b + neg c) (begin≅
        a * (b + neg c)             ≅< left-distribute-on _*_ _+_ a b (neg c) >
        (a * b) + (a * (neg c))     ≅< left-congruent-on _+_ (right-times-neg-on _*_ _+_ 1A 0A neg a c) >
        (a * b) + neg (a * c)       ≅< right-congruent-on _+_ ab=ac >
        (a * c) + neg (a * c)       ≅< right-inverse-on _+_ 0A neg (a * c) >
        0A                          ∎)

cancel-left-multiplication-by-nonzero-on : {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{ID : IntegralDomain _*_ _+_ 1A 0A neg}} →
    (a b c : A) → ¬ (a ≅ 0A) → a * b ≅ a * c → b ≅ c
cancel-left-multiplication-by-nonzero-on {_} {_} {A} _*_ _+_ 1A 0A neg a b c a≠0 ab=ac with cancel-left-multiplication-by-nonzero-helper _*_ _+_ 1A 0A neg a b c ab=ac
... | left a=0      = contradiction-implies-anything (a≠0 a=0)
... | right b-c=0   = symmetric-on A (begin≅
        c               ≅< symmetric-on A (left-identity-on _+_ c) >
        0A + c          ≅< right-congruent-on _+_ (symmetric-on A b-c=0) >
        (b + neg c) + c ≅< right-associate-on _+_ b (neg c) c >
        b + (neg c + c) ≅< left-congruent-on _+_ (left-inverse-on _+_ 0A neg c) >
        b + 0A          ≅< right-identity-on _+_ b >
        b               ∎)

cancel-right-multiplication-by-nonzero-on : {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ : BinOp A) (_+_ : BinOp A) (1A 0A : A) (neg : A → A) → {{ID : IntegralDomain _*_ _+_ 1A 0A neg}} →
    (a b c : A) → ¬ (c ≅ 0A) → a * c ≅ b * c → a ≅ b
cancel-right-multiplication-by-nonzero-on {_} {_} {A} _*_ _+_ 1A 0A neg a b c c≠0 ac=bc = cancel-left-multiplication-by-nonzero-on _*_ _+_ 1A 0A neg c a b c≠0 (begin≅
    c * a           ≅< commute-on _*_ c a >
    a * c           ≅< ac=bc >
    b * c           ≅< commute-on _*_ b c >
    c * b           ∎)