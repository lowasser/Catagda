module Definitions.List where

open import Agda.Primitive
open import Definitions.Function.Binary
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Setoid

open Setoid{{...}}

data [_] { ℓ : Level } (A : Set ℓ) : Set ℓ where
    [] : [ A ]
    _::_ : A → [ A ] → [ A ]

infixr 7 _::_

_++_ : {ℓ : Level} {A : Set ℓ} → BinOp [ A ]
[] ++ list = list
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 6 _++_

[_:] : {ℓ : Level} {A : Set ℓ} → A → [ A ]
[ x :] = x :: []

infix 9 [_:]

map : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (A → B) → [ A ] → [ B ]
map f [] = []
map f (x :: xs) = f x :: map f xs