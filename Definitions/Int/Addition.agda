module Definitions.Int.Addition where

open import Definitions.Function.Binary
open import Definitions.Int
open import Definitions.Nat.Addition renaming (_+_ to _+ℕ_)

_+_ : BinOp ℤ
ℤ< a , b > + ℤ< c , d > = ℤ< a +ℕ c , b +ℕ d >
