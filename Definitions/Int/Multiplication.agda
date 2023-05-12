module Definitions.Int.Multiplication where

open import Definitions.Int
open import Definitions.Nat
open import Definitions.Nat.Addition renaming (_+_ to _+ℕ_)
open import Definitions.Nat.Multiplication renaming (_*_ to _*ℕ_)
open import Definitions.Function.Binary

_*_ : BinOp ℤ
ℤ< a , b > * ℤ< c , d > = ℤ< a *ℕ c +ℕ b *ℕ d , a *ℕ d +ℕ b *ℕ c >