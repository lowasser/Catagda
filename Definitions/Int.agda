module Definitions.Int where

open import Agda.Primitive
open import Definitions.Setoid
open import Agda.Builtin.Unit
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.List
open import Definitions.Setoid.Equation
open import Definitions.List.Setoid {lzero} {lzero} ⊤
open import Definitions.Group.Free {lzero} {lzero} ⊤
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
open import Definitions.Group
open import Definitions.Group.Abelian
open import Definitions.Either
open import Definitions.Either.Setoid {lzero} {lzero} {lzero} {lzero} ⊤ ⊤
open import Definitions.List.Setoid {lzero} {lzero} (Either ⊤ ⊤)
open import Definitions.Function.Unary.Properties
open import Definitions.Ring
open import Definitions.Ring.Commutative
open import Definitions.Ringoid

ℤ : Set
ℤ = FreeGroup ⊤

_+_ : BinOp ℤ
_+_ = _∙_

infixr 9 _+_

pattern 0ℤ = free []

private
    pattern p1 = right tt
    pattern m1 = left tt

suc : ℤ → ℤ
suc (free z) = free (p1 :: z)

negsuc : ℤ → ℤ
negsuc (free z) = free (m1 :: z)

neg : ℤ → ℤ
neg = inverse

pattern 1ℤ = free (p1 :: [])
pattern -1ℤ = free (m1 :: [])

open Setoid {{...}}
open Group {{...}}
open HasInverse {{...}}
open Monoid {{...}}
open Semigroup {{...}}

private
    +-commute-lemma1 : (x : [ Either ⊤ ⊤ ]) → (x1 x2 : Either ⊤ ⊤) → free (x1 :: x2 :: x) ≅ free (x2 :: x1 :: x)
    +-commute-lemma1 x (m1) (m1) = reflexive-on ℤ (free (m1 :: m1 :: x))
    +-commute-lemma1 x (p1) (p1) = reflexive-on ℤ (free (p1 :: p1 :: x))
    +-commute-lemma1 x (m1) (p1) = begin≅
        free (m1 :: p1 :: x)                     ≅<>
        free [ m1 :] + free (p1 :: x)            ≅<>
        free (m1 :: p1 :: []) + free x           ≅<>
        (free [ m1 :] + free [ p1 :]) + free x   ≅< right-congruent-on _+_ (left-inverse-on _+_ 0ℤ inverse (free [ p1 :])) >
        0ℤ + free x                                         ≅< right-congruent-on _+_ (symmetric-on ℤ (right-inverse-on _+_ 0ℤ inverse (free [ p1 :]))) >
        (free [ p1 :] + free [ m1 :]) + free x   ≅<>
        free (p1 :: m1 :: x)                     ∎ 
    +-commute-lemma1 x (p1) (m1) = symmetric-on ℤ (+-commute-lemma1 x (m1) (p1))

    +-commute-lemma2 : (x y : [ Either ⊤ ⊤ ]) → (s : Either ⊤ ⊤) → free (s :: x) + free y ≅ free x + free (s :: y)
    +-commute-lemma2 [] y s = begin≅
        free [ s :] + free y   ≅<>
        free (s :: y)           ≅< symmetric-on ℤ (left-identity-on _+_ (free (s :: y))) >
        0ℤ + free (s :: y)      ∎
    +-commute-lemma2 (x1 :: x) y s = begin≅
        free (s :: x1 :: x) + free y            ≅< right-congruent-on _+_ (+-commute-lemma1 x s x1) >
        free (x1 :: s :: x) + free y            ≅<>
        (free [ x1 :] + free (s :: x)) + free y ≅< symmetric-on ℤ (associate-on _+_ (free [ x1 :]) (free (s :: x)) (free y)) >
        free [ x1 :] + (free (s :: x) + free y) ≅< left-congruent-on _+_ {free [ x1 :]} (+-commute-lemma2 x y s) >
        free [ x1 :] + (free x + free (s :: y)) ≅< associate-on _+_ (free [ x1 :]) (free x) (free (s :: y)) >
        (free [ x1 :] + free x) + free (s :: y) ≅<>
        free (x1 :: x) + free (s :: y)          ∎

    +-commute : (x y : ℤ) → (x + y) ≅ (y + x)
    +-commute 0ℤ y = begin≅
        0ℤ + y      ≅< left-identity-on _+_ y >
        y           ≅< symmetric-on ℤ (right-identity-on _+_ y) >
        y + 0ℤ      ∎
    +-commute (free (s :: x)) (free y) = begin≅
        free (s :: x) + free y          ≅<>
        (free [ s :] + free x) + free y ≅< symmetric-on ℤ (associate-on _+_ (free [ s :]) (free x) (free y)) >
        free [ s :] + (free x + free y) ≅< left-congruent-on _+_ {free [ s :]} (+-commute (free x) (free y)) >
        free [ s :] + (free y + free x) ≅< associate-on _+_ (free [ s :]) (free y) (free x) >
        free (s :: y) + free x          ≅< +-commute-lemma2 y x s >
        free y + free (s :: x)          ∎

instance
    +ℤ-commutative : IsCommutative _+_
    +ℤ-commutative = record { commute = +-commute }

    +ℤ-commutative-magma : CommutativeMagma _+_
    +ℤ-commutative-magma = record {}

    +ℤ-commutative-semigroup : CommutativeSemigroup _+_
    +ℤ-commutative-semigroup = record {}

    +ℤ-commutative-monoid : CommutativeMonoid _+_ 0ℤ
    +ℤ-commutative-monoid = record {}

    +ℤ-commutative-group : AbelianGroup _+_ 0ℤ inverse
    +ℤ-commutative-group = record {}

_*_ : BinOp ℤ
0ℤ * _ = 0ℤ
free (p1 :: x) * y = y + (free x * y)
free (m1 :: x) * y = neg y + (free x * y)

infixr 10 _*_

private
    *-left-congruent : LeftCongruent _*_
    *-left-congruent {0ℤ} _ = reflexive-on ℤ 0ℤ
    *-left-congruent {free (p1 :: x)} {b} {c} b=c = begin≅
        free (p1 :: x) * b        ≅<>
        b + (free x * b)          ≅< bi-congruent _+_ b=c (*-left-congruent {free x} {b} {c} b=c) >
        c + (free x * c)          ≅<>
        free (p1 :: x) * c        ∎
    *-left-congruent {free (m1 :: x)} {b} {c} b=c = begin≅
        free (m1 :: x) * b          ≅<>
        neg b + (free x * b)        ≅< bi-congruent _+_ (congruent-on neg b=c) (*-left-congruent {free x} b=c) >
        neg c + (free x * c)        ≅<>
        free (m1 :: x) * c          ∎

    *-left-zero : LeftZero _*_ 0ℤ
    *-left-zero _ = reflexive-on ℤ 0ℤ

    *-right-zero : RightZero _*_ 0ℤ
    *-right-zero 0ℤ = reflexive-on ℤ 0ℤ
    *-right-zero (free (p1 :: x)) = begin≅
        free (p1 :: x) * 0ℤ       ≅<>
        0ℤ + (free x * 0ℤ)              ≅< left-id-on _+_ (free x * 0ℤ) >
        free x * 0ℤ                     ≅< *-right-zero (free x) >
        0ℤ                              ∎
    *-right-zero (free (m1 :: x)) = begin≅
        free (m1 :: x) * 0ℤ        ≅<>
        neg 0ℤ + free x * 0ℤ           ≅<>
        0ℤ + free x * 0ℤ                ≅< left-id-on _+_ (free x * 0ℤ) >
        free x * 0ℤ                     ≅< *-right-zero (free x) >
        0ℤ                              ∎

    *-left-id : LeftIdentity _*_ 1ℤ
    *-left-id x = begin≅
        1ℤ * x      ≅<>
        x + 0ℤ * x  ≅<>
        x + 0ℤ      ≅< right-id-on _+_ x >
        x           ∎

    *-right-id : RightIdentity _*_ 1ℤ
    *-right-id 0ℤ = *-right-zero 1ℤ
    *-right-id (free (p1 :: x)) = begin≅
        free (p1 :: x) * 1ℤ       ≅<>
        1ℤ + (free x * 1ℤ)              ≅< left-congruent-on _+_ (*-right-id (free x)) >
        1ℤ + free x                     ≅<>
        free (p1 :: x)            ∎
    *-right-id (free (m1 :: x)) = begin≅
        free (m1 :: x) * 1ℤ        ≅<>
        -1ℤ + (free x * 1ℤ)             ≅< left-congruent-on _+_ (*-right-id (free x)) >
        -1ℤ + free x                    ≅<>
        free (m1 :: x)             ∎

    *-distributive-+ : (a b c : ℤ) → a * (b + c) ≅ a * b + a * c
    *-distributive-+ 0ℤ _ _ = reflexive-on ℤ 0ℤ
    *-distributive-+ (free (p1 :: a)) b c = begin≅
        free (p1 :: a) * (b + c)          ≅<>
        (b + c) + (free a * (b + c))            ≅< left-congruent-on _+_ (*-distributive-+ (free a) b c) >
        (b + c) + (free a * b + free a * c)     ≅< right-congruent-on _+_ (commute-on _+_ b c) >
        (c + b) + (free a * b + free a * c)     ≅< associate-on _+_ (c + b) (free a * b) (free a * c) >
        ((c + b) + free a * b) + free a * c     ≅< right-congruent-on _+_ (symmetric-on ℤ (associate-on _+_ c b (free a * b))) >
        (c + (b + free a * b)) + free a * c     ≅<>
        (c + free (p1 :: a) * b) + free a * c
                                                ≅< right-congruent-on _+_ (commute-on _+_ c (free (p1 :: a) * b)) >
        (free (p1 :: a) * b + c) + free a * c
                                                ≅< symmetric-on ℤ (associate-on _+_ (free (p1 :: a) * b) c (free a * c)) >
        free (p1 :: a) * b + (c + free a * c)
                                                ≅<>
        free (p1 :: a) * b + free (p1 :: a) * c
                                                ∎
    *-distributive-+ (free (m1 :: a)) b c = begin≅
        free (m1 :: a) * (b + c)                       ≅<>
        neg (b + c) + (free a * (b + c))                    ≅< left-congruent-on _+_ (*-distributive-+ (free a) b c) >
        neg (b + c) + (free a * b + free a * c)             ≅< right-congruent-on _+_ (distribute-inverse-on _+_ 0ℤ neg b c) >
        (neg c + neg b) + (free a * b + free a * c)         ≅< associate-on _+_ (neg c + neg b) (free a * b) (free a * c) >
        ((neg c + neg b) + free a * b) + free a * c         ≅< right-congruent-on _+_ (symmetric-on ℤ (associate-on _+_ (neg c) (neg b) (free a * b))) >
        (neg c + (neg b + free a * b)) + free a * c         ≅<>
        (neg c + (free (m1 :: a) * b)) + free a * c    ≅< right-congruent-on _+_ (commute-on _+_ (neg c) (free (m1 :: a) * b)) >
        (free (m1 :: a) * b + neg c) + free a * c      ≅< symmetric-on ℤ (associate-on _+_ (free (m1 :: a) * b) (neg c) (free a * c)) >
        free (m1 :: a) * b + (neg c + free a * c)      ≅<>
        free (m1 :: a) * b + free (m1 :: a) * c   ∎

    neg-equals-times-neg1 : (a : ℤ) → a * -1ℤ ≅ neg a
    neg-equals-times-neg1 0ℤ = reflexive-on ℤ 0ℤ
    neg-equals-times-neg1 (free (p1 :: a)) = begin≅
        free (p1 :: a) * -1ℤ            ≅<>
        -1ℤ + (free a * -1ℤ)            ≅< left-congruent-on _+_ (neg-equals-times-neg1 (free a)) >
        -1ℤ + neg (free a)              ≅< commute-on _+_ -1ℤ (neg (free a)) >
        neg (free a) + -1ℤ              ≅<>
        neg (free a) + neg 1ℤ           ≅< symmetric-on ℤ (distribute-inverse-on _+_ 0ℤ neg 1ℤ (free a)) >
        neg (1ℤ + free a)               ≅<>
        neg (free (p1 :: a))            ∎
    neg-equals-times-neg1 (free (m1 :: a)) = begin≅
        free (m1 :: a) * -1ℤ            ≅<>
        1ℤ + (free a * -1ℤ)             ≅< left-congruent-on _+_ (neg-equals-times-neg1 (free a)) >
        1ℤ + neg (free a)               ≅<>
        neg -1ℤ + neg (free a)          ≅< commute-on _+_ (neg -1ℤ) (neg (free a)) >
        neg (free a) + neg -1ℤ          ≅< symmetric-on ℤ (distribute-inverse-on _+_ 0ℤ neg -1ℤ (free a)) >
        neg (-1ℤ + free a)              ≅<>
        neg (free (m1 :: a))            ∎

    *-commute : Commute _*_
    *-commute 0ℤ b = symmetric-on ℤ (*-right-zero b)
    *-commute (free (p1 :: a)) b = begin≅
        free (p1 :: a) * b          ≅<>
        b + free a * b              ≅< left-congruent-on _+_ (*-commute (free a) b) >
        b + b * free a              ≅< right-congruent-on _+_ (symmetric-on ℤ (*-right-id b)) >
        (b * 1ℤ) + (b * free a)     ≅< symmetric-on ℤ (*-distributive-+ b 1ℤ (free a)) >
        b * (1ℤ + free a)           ≅<>
        b * free (p1 :: a)          ∎
    *-commute (free (m1 :: a)) b = begin≅
        free (m1 :: a) * b          ≅<>
        neg b + (free a * b)        ≅< left-congruent-on _+_ (*-commute (free a) b) >
        neg b + (b * free a)        ≅< right-congruent-on _+_ (symmetric-on ℤ (neg-equals-times-neg1 b)) >
        (b * -1ℤ) + (b * free a)    ≅< symmetric-on ℤ (*-distributive-+ b -1ℤ (free a)) >
        b * (-1ℤ + free a)          ≅<>
        b * free (m1 :: a)          ∎

    *-right-distribute : (a b c : ℤ) → (a + b) * c ≅ a * c + b * c
    *-right-distribute a b c = begin≅
        (a + b) * c             ≅< *-commute (a + b) c >
        c * (a + b)             ≅< *-distributive-+ c a b >
        c * a + c * b           ≅< bi-congruent _+_ (*-commute c a) (*-commute c b) >
        a * c + b * c           ∎

    neg-distribute-left-* : (a b : ℤ) → neg (a * b) ≅ neg a * b
    neg-distribute-left-* a b = symmetric-on ℤ (right-inverse-is-unique-on _+_ 0ℤ neg (a * b) (neg a * b) (begin≅
        a * b + neg a * b       ≅< bi-congruent _+_ (*-commute a b) (*-commute (neg a) b) >
        b * a + b * neg a       ≅< symmetric-on ℤ (*-distributive-+ b a (neg a)) >
        b * (a + neg a)         ≅< *-left-congruent {b} (right-inverse-on _+_ 0ℤ neg a) >
        b * 0ℤ                  ≅< *-right-zero b >
        0ℤ                      ∎))
    
    *-assoc : Associate _*_
    *-assoc 0ℤ _ _ = reflexive-on ℤ 0ℤ
    *-assoc (free (p1 :: a)) b c = begin≅
        free (p1 :: a) * (b * c)        ≅<>
        (b * c) + (free a * (b * c))    ≅< left-congruent-on _+_ (*-assoc (free a) b c) >
        (b * c) + ((free a * b) * c)    ≅< symmetric-on ℤ (*-right-distribute b (free a * b) c) >
        (b + free a * b) * c            ≅<>
        (free (p1 :: a) * b) * c        ∎
    *-assoc (free (m1 :: a)) b c = begin≅
        free (m1 :: a) * (b * c)            ≅<>
        neg (b * c) + (free a * (b * c))    ≅< left-congruent-on _+_ (*-assoc (free a) b c) >
        neg (b * c) + ((free a * b) * c)    ≅< right-congruent-on _+_ (neg-distribute-left-* b c) >
        neg b * c + (free a * b) * c        ≅< symmetric-on ℤ (*-right-distribute (neg b) (free a * b) c) >
        (neg b + free a * b) * c            ≅<>
        (free (m1 :: a) * b) * c            ∎

instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record { commute = *-commute }

    *-bi-congruent : BiCongruent _*_
    *-bi-congruent = bi-congruent-commutative _*_ (λ {a b1 b2} → *-left-congruent {a} {b1} {b2})

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

    *-has-identity : HasIdentity _*_ 1ℤ
    *-has-identity = record { left-identity = *-left-id; right-identity = *-right-id }

    *-monoid : Monoid _*_ 1ℤ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℤ
    *-commutative-monoid = record {}

    ℤ-ringoid : Ringoid _+_ _*_
    ℤ-ringoid = record {left-distribute = *-distributive-+; right-distribute = *-right-distribute}

    ℤ-ring : Ring _+_ _*_ 0ℤ 1ℤ neg
    ℤ-ring = record {}

    ℤ-commutative-ring : CommutativeRing _+_ _*_ 0ℤ 1ℤ neg
    ℤ-commutative-ring = record {}