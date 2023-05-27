module Function.Binary where

open import Agda.Primitive

BinOp : { ℓ : Level } → Set ℓ → Set ℓ
BinOp {ℓ} A = A → A → A