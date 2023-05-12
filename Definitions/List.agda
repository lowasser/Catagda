module Definitions.List where

open import Agda.Primitive
open import Definitions.Function.Binary
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Setoid

open Setoid{{...}}

data [_] { ℓ : Level } (A : Set ℓ) : Set ℓ where
    nil : [ A ]
    _::_ : A → [ A ] → [ A ]

pattern [] = nil

_++_ : {ℓ : Level} {A : Set ℓ} → BinOp [ A ]
nil ++ list = list
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 6 _++_

[_:] : {ℓ : Level} {A : Set ℓ} → A → [ A ]
[ x :] = x :: []

infix 9 [_:]