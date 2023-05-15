module Definitions.Not where

open import Agda.Primitive

infix 3 ¬_

data ⊥ : Set where 

private
    variable
        ℓ : Level

¬_ : Set ℓ → Set ℓ
¬ P = P → ⊥

ByContradiction : Set ℓ → Set ℓ
ByContradiction P = ¬ (¬ P)

by-contradiction-by-example : (P : Set ℓ) → P → ByContradiction P
by-contradiction-by-example _ p contr = contr p