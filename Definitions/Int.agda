module Definitions.Int where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Top
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

ℤ : Set
ℤ = FreeGroup ⊤

_+_ : BinOp ℤ
_+_ = _∙_

infixr 9 _+_

pattern 0ℤ = free []

suc : ℤ → ℤ
suc (free z) = free (right tt :: z)

negsuc : ℤ → ℤ
negsuc (free z) = free (left tt :: z)

neg : ℤ → ℤ
neg = inverse

pattern 1ℤ = free (right tt :: [])
pattern -1ℤ = free (left tt :: [])

open Setoid {{...}}
open Group {{...}}
open HasInverse {{...}}
open Monoid {{...}}
open Semigroup {{...}}

private
    +-commute-lemma1 : (x : [ Either ⊤ ⊤ ]) → (x1 x2 : Either ⊤ ⊤) → free (x1 :: x2 :: x) ≅ free (x2 :: x1 :: x)
    +-commute-lemma1 x (left tt) (left tt) = reflexive-on ℤ (free (left tt :: left tt :: x))
    +-commute-lemma1 x (right tt) (right tt) = reflexive-on ℤ (free (right tt :: right tt :: x))
    +-commute-lemma1 x (left tt) (right tt) = begin≅
        free (left tt :: right tt :: x)                     ≅<>
        free [ left tt :] + free (right tt :: x)            ≅<>
        free (left tt :: right tt :: []) + free x           ≅<>
        (free [ left tt :] + free [ right tt :]) + free x   ≅< right-congruent-on _+_ (left-inverse-on _+_ 0ℤ inverse (free [ right tt :])) >
        0ℤ + free x                                         ≅< right-congruent-on _+_ (symmetric-on ℤ (right-inverse-on _+_ 0ℤ inverse (free [ right tt :]))) >
        (free [ right tt :] + free [ left tt :]) + free x   ≅<>
        free (right tt :: left tt :: x)                     ∎ 
    +-commute-lemma1 x (right tt) (left tt) = symmetric-on ℤ (+-commute-lemma1 x (left tt) (right tt))

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
free (right tt :: x) * y = y + (free x * y)
free (left tt :: x) * y = neg y + (free x * y)

infixr 10 _*_

private
    *-left-zero : LeftZero _*_ 0ℤ
    *-left-zero _ = reflexive-on ℤ 0ℤ

    *-right-zero : RightZero _*_ 0ℤ
    *-right-zero 0ℤ = reflexive-on ℤ 0ℤ
    *-right-zero (free (right tt :: x)) = begin≅
        free (right tt :: x) * 0ℤ       ≅<>
        0ℤ + (free x * 0ℤ)              ≅< left-id-on _+_ (free x * 0ℤ) >
        free x * 0ℤ                     ≅< *-right-zero (free x) >
        0ℤ                              ∎
    *-right-zero (free (left tt :: x)) = begin≅
        free (left tt :: x) * 0ℤ        ≅<>
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
    *-right-id (free (right tt :: x)) = begin≅
        free (right tt :: x) * 1ℤ       ≅<>
        1ℤ + (free x * 1ℤ)              ≅< left-congruent-on _+_ (*-right-id (free x)) >
        1ℤ + free x                     ≅<>
        free (right tt :: x)            ∎
    *-right-id (free (left tt :: x)) = begin≅
        free (left tt :: x) * 1ℤ        ≅<>
        -1ℤ + (free x * 1ℤ)             ≅< left-congruent-on _+_ (*-right-id (free x)) >
        -1ℤ + free x                    ≅<>
        free (left tt :: x)             ∎

    *-distributive-+ : (a b c : ℤ) → a * (b + c) ≅ a * b + a * c
    *-distributive-+ 0ℤ _ _ = reflexive-on ℤ 0ℤ
    *-distributive-+ (free (right tt :: a)) b c = begin≅
        free (right tt :: a) * (b + c)          ≅<>
        (b + c) + (free a * (b + c))            ≅< left-congruent-on _+_ (*-distributive-+ (free a) b c) >
        (b + c) + (free a * b + free a * c)     ≅< right-congruent-on _+_ (commute-on _+_ b c) >
        (c + b) + (free a * b + free a * c)     ≅< associate-on _+_ (c + b) (free a * b) (free a * c) >
        ((c + b) + free a * b) + free a * c     ≅< right-congruent-on _+_ (symmetric-on ℤ (associate-on _+_ c b (free a * b))) >
        (c + (b + free a * b)) + free a * c     ≅<>
        (c + free (right tt :: a) * b) + free a * c
                                                ≅< right-congruent-on _+_ (commute-on _+_ c (free (right tt :: a) * b)) >
        (free (right tt :: a) * b + c) + free a * c
                                                ≅< symmetric-on ℤ (associate-on _+_ (free (right tt :: a) * b) c (free a * c)) >
        free (right tt :: a) * b + (c + free a * c)
                                                ≅<>
        free (right tt :: a) * b + free (right tt :: a) * c
                                                ∎
    *-distributive-+ (free (left tt :: a)) b c = begin≅
        free (left tt :: a) * (b + c)                       ≅<>
        neg (b + c) + (free a * (b + c))                    ≅< left-congruent-on _+_ (*-distributive-+ (free a) b c) >
        neg (b + c) + (free a * b + free a * c)             ≅< right-congruent-on _+_ (distribute-inverse-on _+_ 0ℤ neg b c) >
        (neg c + neg b) + (free a * b + free a * c)         ≅< associate-on _+_ (neg c + neg b) (free a * b) (free a * c) >
        ((neg c + neg b) + free a * b) + free a * c         ≅< right-congruent-on _+_ (symmetric-on ℤ (associate-on _+_ (neg c) (neg b) (free a * b))) >
        (neg c + (neg b + free a * b)) + free a * c         ≅<>
        (neg c + (free (left tt :: a) * b)) + free a * c    ≅< right-congruent-on _+_ (commute-on _+_ (neg c) (free (left tt :: a) * b)) >
        (free (left tt :: a) * b + neg c) + free a * c      ≅< symmetric-on ℤ (associate-on _+_ (free (left tt :: a) * b) (neg c) (free a * c)) >
        free (left tt :: a) * b + (neg c + free a * c)      ≅<>
        free (left tt :: a) * b + free (left tt :: a) * c   ∎

    *-left-congruent : LeftCongruent _*_
    *-left-congruent {0ℤ} _ = reflexive-on ℤ 0ℤ
    *-left-congruent {free (right tt :: x)} {b} {c} b=c = begin≅
        free (right tt :: x) * b        ≅<>
        b + (free x * b)                ≅< left-congruent-on _+_ (*-left-congruent {free x} {b} {c} b=c) >
        b + (free x * c)                ≅< right-congruent-on _+_ b=c >
        c + (free x * c)                ≅<>
        free (right tt :: x) * c        ∎