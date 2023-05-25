open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Monoid.Commutative.Free {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Definitions.Function.Binary
open import Agda.Builtin.Sigma
open import Definitions.Either
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Nat renaming (_≅_ to _=N_ )
open import Definitions.Function.Properties
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Setoid.Decidable
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.Pair
open import Definitions.Logic
open import Definitions.Setoid
open import Definitions.Setoid.Equation

data FreeCommutativeMonoid : Set ℓA → Set (ℓA ⊔ ℓ=A) where
    fcm : (A Congruent→ ℕ) → FreeCommutativeMonoid A

data _≈_ : Rel (ℓA ⊔ ℓ=A) (FreeCommutativeMonoid A) where
    fcm= : {f g : A Congruent→ ℕ} → Pointwise= A ℕ f g → fcm f ≈ fcm g

instance
    fcm-setoid : Setoid (ℓA ⊔ ℓ=A) (FreeCommutativeMonoid A)
    fcm-setoid = make-setoid _≈_ ≈-refl ≈-trans ≈-sym where
        instance
            cong-setoid = congruent-setoid A ℕ
        ≈-refl : Reflexive _≈_
        ≈-refl (fcm f) = fcm= (reflexive-on (A Congruent→ ℕ) f)
        ≈-sym : Symmetric _≈_
        ≈-sym (fcm= f=g) = fcm= (symmetric-on (A Congruent→ ℕ) f=g)
        ≈-trans : Transitive _≈_
        ≈-trans (fcm= f=g) (fcm= g=h) = fcm= (transitive-on (A Congruent→ ℕ) f=g g=h)

open DecidableSetoid {{...}}
open Setoid {{...}}
open Decidable {{...}}

private
    _=A_ = Setoid._≅_ SA

    _,,_ : {ℓX ℓY : Level} {X : Set ℓX} {Y : Set ℓY} → X → Y → X × Y
    _,,_ = _,_
{-
proj : {{D : Decidable _=A_}} → A → FreeCommutativeMonoid A
proj a = fcm (record { cong-func = f })
    where   dec : (x y : A) → (x =A y) ∨ ¬ (x =A y)
            dec = decide
            
            f' : (x : A) → (x =A a ∨ ¬ (x =A a)) → ℕ
            f' x (left _) = 1ℕ
            f' x (right _) = 0ℕ
            f : A → ℕ
            f x = f' x (dec x a)

            congruent-f : Congruent f
            congruent-f {b} {c} b=c with dec b a | dec c a 
            ... | left b=a | left c=a = begin≅
                    f b                 ≅<>
                    f' b (left b=a)     ≅<>
                    1ℕ                  ≅<>
                    f' c (left c=a)     ≅<>
                    f' c (dec c a)      ≅<>
                    f c                 ∎

_∙_ : BinOp (FreeCommutativeMonoid A)
fcm f ∙ fcm g = fcm (pointwise-congruent f g _+_)
 
private
    ∙-left-congruent : LeftCongruent _∙_   -}