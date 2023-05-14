open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Monoid.Free {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.List
open import Definitions.List.Setoid {ℓA} {ℓ=A} (A)
open import Definitions.List.Properties {ℓA} {ℓ=A} (A)
open import Definitions.List.Concatenation.Properties {ℓA} {ℓ=A} (A)
open import Definitions.Semigroup
open import Definitions.Setoid.Equation
open import Definitions.Monoid

FreeMonoid : Set ℓA → Set ℓA
FreeMonoid A = [ A ]

_∙_ : BinOp (FreeMonoid A)
_∙_ = _++_