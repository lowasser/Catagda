module Definitions.Nat.Multiplication where

open import Definitions.Nat
open import Definitions.Nat.Addition
open import Definitions.Function.Binary

_*_ : BinOp ℕ
0 * _ = 0
suc m * n = n + (m * n)

infixr 12 _*_