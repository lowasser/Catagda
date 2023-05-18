module Definitions.Int where

open import Agda.Primitive
open import Definitions.Setoid
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
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
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Order.Partial
open import Definitions.Relation.Order.Total
open import Definitions.Logic
open import Definitions.Pair

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

