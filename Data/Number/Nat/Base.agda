module Data.Number.Nat.Base where

open import Agda.Primitive
open import Data.List
open import Agda.Builtin.Unit
open import Relation.Equivalence.Structural
open import Relation
open import Structure.Setoid
open import Relation.Equivalence.Structural.Properties ⊤
open import Data.List.Setoid {lzero} {lzero} ⊤
open import Structure.Algebraic.Monoid.Free {lzero} {lzero} ⊤
open import Data.List.Properties {lzero} {lzero} ⊤
open import Function.Unary.Properties
open import Function.Binary.Properties

ℕ : Set
ℕ = FreeMonoid ⊤

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
 