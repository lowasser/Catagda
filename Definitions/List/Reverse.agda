module Definitions.List.Reverse where

open import Agda.Primitive
open import Definitions.List

reverse : {ℓ : Level} {A : Set ℓ} → [ A ] → [ A ]
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x :]
