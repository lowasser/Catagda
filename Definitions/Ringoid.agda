module Definitions.Ringoid where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

open Setoid {{...}}

private
    variable
        ℓA ℓ=A : Level 

record Ringoid {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_*_ _+_ : BinOp A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        left-distribute : (a b c : A) → a * (b + c) ≅ (a * b) + (a * c)
        right-distribute : (a b c : A) → (a + b) * c ≅ (a * c) + (b * c)

commuting-ringoid : {A : Set ℓA} {{SA : Setoid ℓ=A A}} → {_*_ _+_ : BinOp A} → ((a b c : A) → a * (b + c) ≅ (a * b) + (a * c)) → {{IC : IsCommutative _*_}} → {{BC : BiCongruent _+_}} → Ringoid _*_ _+_
commuting-ringoid {_} {_} {A} {_*_} {_+_} left-distribute = record {left-distribute = left-distribute; right-distribute = right-distribute} where
    right-distribute : (a b c : A) → (a + b) * c ≅ (a * c) + (b * c)
    right-distribute a b c = begin≅
        (a + b) * c         ≅< commute-on _*_ (a + b) c >
        c * (a + b)         ≅< left-distribute c a b >
        (c * a) + (c * b)   ≅< bi-congruent _+_ (commute-on _*_ c a) (commute-on _*_ c b) >
        (a * c) + (b * c)   ∎

left-distribute-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_*_ _+_ : BinOp A) → {{R : Ringoid _*_ _+_}} → (a b c : A) → a * (b + c) ≅ (a * b) + (a * c)
left-distribute-on _ _ {{R}} = Ringoid.left-distribute R

right-distribute-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_*_ _+_ : BinOp A) → {{R : Ringoid _*_ _+_}} → (a b c : A) → (a + b) * c ≅ (a * c) + (b * c)
right-distribute-on _ _ {{R}} = Ringoid.right-distribute R