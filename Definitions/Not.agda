module Definitions.Not where

infix 3 ¬_

data ⊥ : Set where 

¬_ : Set → Set
¬ P = P → ⊥