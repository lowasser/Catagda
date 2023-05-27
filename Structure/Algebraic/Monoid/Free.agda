open import Agda.Primitive
open import Structure.Setoid

module Structure.Algebraic.Monoid.Free {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Structure.Algebraic.Magma
open import Function.Binary
open import Function.Binary.Properties
open import Relation
open import Relation.Properties
open import Data.List
open import Data.List.Setoid {ℓA} {ℓ=A} (A)
open import Data.List.Properties {ℓA} {ℓ=A} (A)
open import Data.List.Concatenation.Properties {ℓA} {ℓ=A} (A)
open import Structure.Algebraic.Semigroup
open import Structure.Setoid.Equation
open import Structure.Algebraic.Monoid

FreeMonoid : Set ℓA → Set ℓA
FreeMonoid A = [ A ]

_∙_ : BinOp (FreeMonoid A)
_∙_ = _++_