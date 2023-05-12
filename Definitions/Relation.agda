module Definitions.Relation where

open import Agda.Primitive

Relation : {L : Level} → (A : Set L) → Set (lsuc lzero ⊔ lsuc L)
Relation {L} A = A → A → Set L