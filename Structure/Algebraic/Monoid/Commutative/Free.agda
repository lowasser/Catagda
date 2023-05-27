open import Agda.Primitive
open import Structure.Setoid

module Structure.Algebraic.Monoid.Commutative.Free {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Function.Binary
open import Agda.Builtin.Sigma
open import Data.Either
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative
open import Data.Number.Nat renaming (_≅_ to _=N_ )
open import Function.Properties
open import Relation
open import Relation.Properties
open import Structure.Setoid.Decidable
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Data.Pair
open import Logic
open import Structure.Setoid
open import Structure.Setoid.Equation

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