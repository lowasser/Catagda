module Definitions.Function where

open import Agda.Primitive

id : {ℓ : Level} {A : Set ℓ} → A → A
id x = x