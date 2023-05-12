open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Monoid.Free {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} where

open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Isomorphism
open import Definitions.Relation
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Properties
open import Definitions.List
open import Definitions.List.Setoid (A)
open import Definitions.List.Properties (A)
open import Definitions.List.Concatenation.Properties (A)
open import Definitions.Semigroup
open import Definitions.Setoid.Equation
open import Definitions.Monoid

FreeMonoid : Set ℓ → Set ℓ
FreeMonoid A = [ A ]
