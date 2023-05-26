module Definitions.Nat.Base where

open import Definitions.Monoid
open import Agda.Primitive
open import Definitions.List
open import Agda.Builtin.Unit
open import Definitions.Function.Binary
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation
open import Definitions.Setoid
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.List.Setoid {lzero} {lzero} ⊤
open import Definitions.Monoid.Free {lzero} {lzero} ⊤
open import Definitions.List.Properties {lzero} {lzero} ⊤
open import Definitions.List.Concatenation.Properties {lzero} {lzero} ⊤
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Magma
open import Definitions.Semigroup

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