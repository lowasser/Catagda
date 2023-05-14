module Definitions.Not where

open import Agda.Primitive

infix 3 ¬_

data ⊥ : Set where 

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → ⊥