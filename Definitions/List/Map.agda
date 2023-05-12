module Definitions.List.Map where

open import Agda.Primitive 
open import Definitions.List

map : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (A → B) → [ A ] → [ B ]