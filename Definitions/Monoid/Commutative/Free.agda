open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Monoid.Commutative.Free {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} where

open import Definitions.Function.Binary
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Nat
open import Definitions.Nat.Addition

open import Definitions.Function.Properties A ℕ

data FreeCommutativeMonoid : Set (lsuc ℓ) where
    fcm : (A Congruent→ ℕ) → FreeCommutativeMonoid

data _==_ : FreeCommutativeMonoid → FreeCommutativeMonoid → Set (lsuc ℓ) where
    equiv : {f g : A Congruent→ ℕ} → f ≡→ g → fcm f == fcm g

_+→_ : (A → ℕ) → (A → ℕ) → A → ℕ
f +→ g = λ x → f x + g x