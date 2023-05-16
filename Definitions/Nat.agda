module Definitions.Nat where

open import Agda.Primitive
open import Definitions.Setoid
open import Agda.Builtin.Unit
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.List
open import Definitions.Setoid.Equation
open import Definitions.List.Setoid {lzero} {lzero} ⊤
open import Definitions.Monoid.Free {lzero} {lzero} ⊤
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Monoid
open import Definitions.List.Properties {lzero} {lzero} ⊤
open import Definitions.List.Concatenation.Properties {lzero} {lzero} ⊤
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid.Commutative
open import Definitions.Ringoid

open Monoid {{...}}

ℕ : Set
ℕ = FreeMonoid ⊤

_+_ : BinOp ℕ
a + b = a ∙ b

infixr 9 _+_

pattern zero = []
pattern 0ℕ = zero
pattern suc n = (tt :: n)
pattern 1ℕ = suc 0ℕ

open Setoid {{...}}

private
    +-commute-lemma : (x y : ℕ) → (suc x + y) ≅ (x + suc y)
    +-commute-lemma zero y = begin≅
        suc zero + y        ≅<>
        [ tt :] + y         ≅<>
        tt :: y             ≅<>
        suc y               ≅< symmetric-on ℕ (left-identity-on _+_ (suc y)) >
        zero + suc y        ∎
    +-commute-lemma (suc x) y = begin≅
        suc (suc x) + y     ≅<>
        suc (suc x + y)     ≅< left-congruent-on _::_ (+-commute-lemma x y) >
        suc (x + suc y)     ≅<>
        suc x + suc y       ∎

    +-commute : Commute _+_
    +-commute [] ys = begin≅
        [] ++ ys            ≅<>
        ys                  ≅< symmetric-on ℕ (right-identity-on _++_ ys) >
        ys ++ []            ∎
    +-commute (suc x) y = begin≅
        suc x + y           ≅<>
        suc (x + y)         ≅< left-congruent-on _::_ (+-commute x y) >
        suc (y + x)         ≅<>
        suc y + x           ≅< +-commute-lemma y x >
        y + suc x           ∎

instance
    +-commutative : IsCommutative  _+_
    +-commutative = record {commute = +-commute}

    +-commutative-magma : CommutativeMagma _+_
    +-commutative-magma = record {}

    +-commutative-semigroup : CommutativeSemigroup _+_
    +-commutative-semigroup = record {}

    +-commutative-monoid : CommutativeMonoid _+_ zero
    +-commutative-monoid = record {}

_*_ : BinOp ℕ
zero * n = zero
suc m * n = n + (m * n)

infixr 10 _*_

private
    *-left-congruent : LeftCongruent _*_
    *-left-congruent {zero} {_} {_} _ = reflexive-on ℕ zero
    *-left-congruent {suc a} {b} {c} b=c = bi-congruent _+_ b=c (*-left-congruent {a} {b} {c} b=c)

    *-left-zero : LeftZero _*_ zero
    *-left-zero x = reflexive-on ℕ zero

    *-right-zero : RightZero _*_ zero
    *-right-zero zero = reflexive-on ℕ zero
    *-right-zero (suc n) = begin≅
        suc n * zero        ≅<>
        zero + (n * zero)   ≅<>
        n * zero            ≅< *-right-zero n >
        zero                ∎

    *-distributes-over-+ : (a b c : ℕ) → a * (b + c) ≅ a * b + a * c
    *-distributes-over-+ zero _ _ = reflexive-on ℕ zero
    *-distributes-over-+ (suc a) b c = begin≅
        suc a * (b + c)             ≅<>
        (b + c) + a * (b + c)       ≅< left-congruent-on _+_ (*-distributes-over-+ a b c) >
        (b + c) + (a * b + a * c)   ≅< right-congruent-on _+_ (+-commute b c) >
        (c + b) + (a * b + a * c)   ≅< associate-on _+_ (c + b) (a * b) (a * c) >
        ((c + b) + a * b) + a * c   ≅< right-congruent-on _+_ (symmetric-on ℕ (associate-on _+_ c b (a * b))) >
        (c + (b + a * b)) + a * c   ≅<>
        (c + suc a * b) + a * c     ≅< right-congruent-on _+_ (+-commute c (suc a * b)) >
        (suc a * b + c) + a * c     ≅< symmetric-on ℕ (associate-on _+_ (suc a * b) c (a * c)) >
        suc a * b + (c + a * c)     ≅<>
        suc a * b + suc a * c       ∎

    *-left-id : LeftIdentity _*_ 1ℕ
    *-left-id zero = reflexive-on ℕ zero
    *-left-id (suc n) = begin≅
        1ℕ * suc n              ≅<>
        suc n + (0ℕ * suc n)    ≅<>
        suc n + 0ℕ              ≅< right-identity-on _+_ (suc n) >
        suc n                   ∎

    *-right-id : RightIdentity _*_ 1ℕ
    *-right-id zero = reflexive-on ℕ zero
    *-right-id (suc n) = begin≅
        suc n * 1ℕ              ≅<>
        1ℕ + (n * 1ℕ)           ≅< left-congruent-on _+_ (*-right-id n) >
        1ℕ + n                  ≅<>
        suc n                   ∎
    
    *-commute : Commute _*_
    *-commute zero n = begin≅
        zero * n            ≅<>
        zero                ≅< symmetric-on ℕ (*-right-zero n) >
        n * zero            ∎
    *-commute (suc m) n = begin≅
        suc m * n           ≅<>
        n + (m * n)         ≅< left-congruent-on _+_ (*-commute m n) >
        n + (n * m)         ≅< right-congruent-on _+_ (symmetric-on ℕ (*-right-id n)) >
        (n * 1ℕ) + (n * m)  ≅< symmetric-on ℕ (*-distributes-over-+ n 1ℕ m) >
        n * (1ℕ + m)        ≅<>
        n * suc m           ∎

    *-right-distributes : (a b c : ℕ) → (a + b) * c ≅ a * c + b * c
    *-right-distributes a b c = begin≅
        (a + b) * c         ≅< *-commute (a + b) c >
        c * (a + b)         ≅< *-distributes-over-+ c a b >
        c * a + c * b       ≅< bi-congruent _+_ (*-commute c a) (*-commute c b) >
        a * c + b * c       ∎

    *-assoc : Associate _*_
    *-assoc zero b c = begin≅
        zero * (b * c)      ≅<>
        zero                ≅<>
        zero * c            ≅<>
        (zero * b) * c      ∎
    *-assoc (suc a) b c = begin≅
        suc a * (b * c)                     ≅<>
        b * c + a * (b * c)                 ≅< left-congruent-on _+_ (*-assoc a b c) >
        b * c + (a * b) * c                 ≅< symmetric-on ℕ (*-right-distributes b (a * b) c) >
        (b + a * b) * c                     ≅<>
        (suc a * b) * c                     ∎

        
instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record { commute = *-commute }

    *-bicong : BiCongruent _*_
    *-bicong = bi-congruent-commutative _*_ (λ {a b c} b=c → *-left-congruent {a} {b} {c} b=c)

    *-magma : Magma _*_
    *-magma = record {}

    *-commutative-magma : CommutativeMagma _*_
    *-commutative-magma = record {}

    *-is-associative : IsAssociative _*_
    *-is-associative = record { associate = *-assoc }

    *-semigroup : Semigroup _*_
    *-semigroup = record {}

    *-commutative-semigroup : CommutativeSemigroup _*_
    *-commutative-semigroup = record {}

    *-has-identity : HasIdentity _*_ 1ℕ
    *-has-identity = record { left-identity = *-left-id ; right-identity = *-right-id }

    *-monoid : Monoid _*_ 1ℕ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℕ
    *-commutative-monoid = record {}

    *-ringoid : Ringoid _+_ _*_
    *-ringoid = record { left-distribute = *-distributes-over-+ ; right-distribute = *-right-distributes }