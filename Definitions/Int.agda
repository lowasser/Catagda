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

pattern 0ℤ = free []

sucℤ : ℤ → ℤ
sucℤ (free z) = free (right tt :: z)

negsucZ : ℤ → ℤ
negsucZ (free z) = free (left tt :: z)

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