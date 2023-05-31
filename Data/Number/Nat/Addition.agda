module Data.Number.Nat.Addition where

open import Structure.Algebraic.Monoid
open import Agda.Primitive
open import Data.List
open import Agda.Builtin.Unit
open import Structure.Setoid
open import Relation.Equivalence.Structural.Properties ⊤
open import Structure.Algebraic.Monoid.Free {lzero} {lzero} ⊤
open import Data.List.Concatenation.Properties {lzero} {lzero} ⊤
open import Function.Unary.Properties
open import Function.Binary.Properties
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Monoid.Commutative
open import Data.Number.Nat.Base
open import Structure.Setoid.Equation
open import Function.Binary

_+_ : BinOp ℕ
a + b = a ∙ b

infixr 9 _+_

instance
    ℕ+-monoid : Monoid _+_ 0ℕ
    ℕ+-monoid = ++-monoid

    +-has-identity : HasIdentity _+_ 0ℕ
    +-has-identity = ++-has-identity
    
    +-bi-congruent : BiCongruent _+_
    +-bi-congruent = ++-bi-congruent

    ℕ+-magma : Magma _+_
    ℕ+-magma = ++-magma

    ℕ+-semigroup : Semigroup _+_
    ℕ+-semigroup = ++-semigroup

    ℕ+-is-associative : IsAssociative _+_
    ℕ+-is-associative = ++-is-associative


private
    +-commute-lemma : (x y : ℕ) → (suc x + y) ≅ (x + suc y)
    +-commute-lemma 0ℕ y = begin≅
        1ℕ + y              ≅<>
        suc y               ≅< symmetric-on ℕ (left-identity-on _+_ (suc y)) >
        0ℕ + suc y          ∎
    +-commute-lemma (suc x) y = begin≅
        suc (suc x) + y     ≅<>
        suc (suc x + y)     ≅< congruent-on suc (+-commute-lemma x y) >
        suc (x + suc y)     ≅<>
        suc x + suc y       ∎

    +-commute : Commute _+_
    +-commute 0ℕ ys = begin≅
        0ℕ + ys            ≅<>
        ys                  ≅< symmetric-on ℕ (right-identity-on _++_ ys) >
        ys + 0ℕ            ∎
    +-commute (suc x) y = begin≅
        suc x + y           ≅<>
        suc (x + y)         ≅< congruent-on suc (+-commute x y) >
        suc (y + x)         ≅<>
        suc y + x           ≅< +-commute-lemma y x >
        y + suc x           ∎

    +-left-injective : (a : ℕ) → Injective (a +_)
    +-left-injective 0ℕ ab=ac = ab=ac
    +-left-injective (suc a) (suc= ab=ac) = +-left-injective a ab=ac

    +-right-injective : (a : ℕ) → Injective (_+ a)
    +-right-injective a {b} {c} ba=ca = +-left-injective a (begin≅
        a + b       ≅< +-commute a b >
        b + a       ≅< ba=ca >
        c + a       ≅< +-commute c a >
        a + c       ∎)

instance
    +-commutative : IsCommutative  _+_
    +-commutative = record {commute = +-commute}

    +-commutative-magma : CommutativeMagma _+_
    +-commutative-magma = record {}

    +-commutative-semigroup : CommutativeSemigroup _+_
    +-commutative-semigroup = record {}

    +-commutative-monoid : CommutativeMonoid _+_ 0ℕ
    +-commutative-monoid = record {}

    +-bi-injective : BiInjective _+_
    +-bi-injective = record {left-injective = +-left-injective; right-injective = +-right-injective}