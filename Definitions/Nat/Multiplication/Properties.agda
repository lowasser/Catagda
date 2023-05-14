module Definitions.Nat.Multiplication.Properties where

open import Definitions.Nat
open import Definitions.Nat.Addition
open import Definitions.Nat.Addition.Properties
open import Definitions.Nat.Multiplication
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Relation.Equivalence.Structural.Properties (ℕ)
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Setoid
open import Definitions.Setoid.Equation

open Setoid {{...}}

instance
    *-IsBiCongruent : BiCongruent _*_
    *-IsBiCongruent = ≡-bi-congruent _*_

    *-Magma : Magma _*_
    *-Magma = record {}

private
    *-+-distribute : (x y z : ℕ) → x * (y + z) ≅ x * y + x * z
    *-+-distribute 0 y z = begin≅
        0 * (y + z)         ≅<>
        0                   ≅< symmetric-on ℕ (left-identity-on _+_ 0) >
        0 + 0               ≅<>
        0 * y + 0 * z       ∎
    *-+-distribute (suc x) y z = begin≅
        suc x * (y + z)             ≅<>
        (y + z) + (x * (y + z))     ≅< left-congruent-on _+_ (*-+-distribute x y z) >
        (y + z) + (x * y + x * z)   ≅< right-congruent-on _+_ (commute-on _+_ y z) >
        (z + y) + (x * y + x * z)   ≅< symmetric-on ℕ (associate-on _+_ z y (x * y + x * z)) >
        z + (y + (x * y + x * z))   ≅< left-congruent-on _+_ {z} (associate-on _+_ y (x * y) (x * z)) >
        z + ((y + x * y) + x * z)   ≅<>
        z + (suc x * y + x * z)     ≅< commute-on _+_ z (suc x * y + x * z) >
        (suc x * y + x * z) + z     ≅< symmetric-on ℕ (associate-on _+_ (suc x * y) (x * z) z) >
        suc x * y + (x * z + z)     ≅< left-congruent-on _+_ {suc x * y} (commute-on _+_ (x * z) z) >
        suc x * y + (z + x * z)     ≅<>
        suc x * y + suc x * z       ∎

    *-left-zero : LeftZero _*_ 0
    *-left-zero _ = reflexive-on ℕ 0

    *-right-zero : RightZero _*_ 0
    *-right-zero 0 = reflexive-on ℕ 0
    *-right-zero (suc x) = begin≅
        suc x * 0       ≅<>
        0 + (x * 0)     ≅<>
        x * 0           ≅< *-right-zero x >
        0               ∎

    *-mostly-left-id : (n : ℕ) → 1 * suc n ≅ suc n 
    *-mostly-left-id 0 = reflexive-on ℕ 1
    *-mostly-left-id (suc n) = begin≅
        1 * suc (suc n)                     ≅<>
        suc (suc n) + (0 * suc (suc n))     ≅<>
        suc (suc n) + 0                     ≅< right-id-on _+_ (suc (suc n)) >
        suc (suc n)                         ∎

    *-mostly-right-id : (n : ℕ) → suc n * 1 ≅ suc n 
    *-mostly-right-id 0 = reflexive-on ℕ 1
    *-mostly-right-id (suc n) = begin≅
        suc (suc n) * 1         ≅<>
        1 + (suc n * 1)         ≅<>
        suc (suc n * 1)         ≅< congruent-on suc (*-mostly-right-id n) >
        suc (suc n)             ∎

    *-commute : Commute _*_
    *-commute 0 n = begin≅
        0 * n       ≅<>
        0           ≅< symmetric-on ℕ (*-right-zero n) >
        n * 0       ∎
    *-commute m 0 = begin≅
        m * 0       ≅< *-right-zero m >
        0           ≅<>
        0 * m       ∎
    *-commute (suc m) (suc n) = begin≅
        suc m * suc n               ≅<>
        suc n + (m * suc n)         ≅< left-congruent-on _+_ (*-commute m (suc n)) >
        suc n + (suc n * m)         ≅< right-congruent-on _+_ (symmetric-on ℕ (*-mostly-right-id n)) >
        (suc n * 1) + (suc n * m)   ≅< symmetric-on ℕ (*-+-distribute (suc n) 1 m) >
        suc n * (1 + m)             ≅<>
        suc n * suc m               ∎

    *-assoc : Associate _*_ 
    *-assoc 0 y z = begin≅
        0 * (y * z)     ≅<>
        0               ≅<>
        0 * z           ≅<>
        (0 * y) * z     ∎
    *-assoc (suc x) y z = begin≅
        suc x * (y * z)             ≅<>
        (y * z) + (x * (y * z))     ≅< left-congruent-on _+_ (*-assoc x y z) >
        (y * z) + ((x * y) * z)     ≅< right-congruent-on _+_ (*-commute y z) >
        (z * y) + ((x * y) * z)     ≅< left-congruent-on _+_ (*-commute (x * y) z) >
        (z * y) + (z * (x * y))     ≅< symmetric-on ℕ (*-+-distribute z y (x * y)) >
        z * (y + (x * y))           ≅<>
        z * (suc x * y)             ≅< *-commute z (suc x * y) >
        (suc x * y) * z             ∎

instance
    *-Zero : HasZero _*_ 0
    *-Zero = record {left-zero = *-left-zero; right-zero = *-right-zero}

    *-Commutative : IsCommutative _*_
    *-Commutative = record {commute = *-commute}

    *-Associative : IsAssociative _*_
    *-Associative = record {associate = *-assoc}

    *-Semigroup : Semigroup _*_
    *-Semigroup = record {}

    *-CommutativeMagma : CommutativeMagma _*_ 
    *-CommutativeMagma = record {}

    *-CommutativeSemigroup : CommutativeSemigroup _*_
    *-CommutativeSemigroup = record {}