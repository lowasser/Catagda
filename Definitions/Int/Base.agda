module Definitions.Int.Base where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Definitions.List
open import Definitions.Either
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.Group.Free {lzero} {lzero} ⊤

ℤ : Set
ℤ = FreeGroup ⊤

pattern 0ℤ = free []
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
