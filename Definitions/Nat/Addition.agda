module Definitions.Nat.Addition where

open import Definitions.Nat
open import Definitions.Function.Binary

_+_ : BinOp ℕ
zero + n = n
suc m + n = suc (m + n)

infixr 11 _+_