module Data.Number.Nat.Base where

open import Structure.Algebraic.Monoid
open import Agda.Primitive
open import Data.List
open import Agda.Builtin.Unit
open import Function.Binary
open import Relation.Equivalence.Structural
open import Relation
open import Structure.Setoid
open import Relation.Equivalence.Structural.Properties ⊤
open import Data.List.Setoid {lzero} {lzero} ⊤
open import Structure.Algebraic.Monoid.Free {lzero} {lzero} ⊤
open import Data.List.Properties {lzero} {lzero} ⊤
open import Data.List.Concatenation.Properties {lzero} {lzero} ⊤
open import Function.Unary.Properties
open import Function.Binary.Properties
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Semigroup

open Monoid {{...}}

ℕ : Set
ℕ = FreeMonoid ⊤

_+_ : BinOp ℕ
a + b = a ∙ b

infixr 9 _+_

pattern 0ℕ = []
pattern suc n = (tt :: n)
pattern 1ℕ = suc 0ℕ
pattern suc= x=y = (cons=[]=cons refl x=y)
pattern 0ℕ= = []=[]

_≅_ : Rel lzero ℕ
_≅_ = _=[]=_

infix 4 _≅_

private
    suc-injective : Injective suc
    suc-injective (suc= x=y) = x=y

instance
    suc-is-injective : IsInjective suc
    suc-is-injective = record {injective = suc-injective}

    ℕ-setoid : Setoid lzero ℕ
    ℕ-setoid = []-setoid

    suc-is-congruent : IsCongruent suc
    suc-is-congruent = record { congruent = left-congruent-on _::_}

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