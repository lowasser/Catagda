open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Function.Properties {ℓA ℓB : Level} (A : Set ℓA) (B : Set ℓB) {{AS : Setoid A}} {{BS : Setoid B}} where

open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Equivalence
open import Definitions.Function.Unary.Properties
open import Definitions.Setoid.Equation

open Setoid {{...}}

data _Congruent→_ : Set ℓA → Set ℓB → Set (lsuc (ℓA ⊔ ℓB)) where
    cong→ : (f : A → B) → Congruent {ℓA} {ℓB} {A} {B} f {{AS}} {{BS}} → A Congruent→ B
 
_cong$_ : A Congruent→ B → A → B
(cong→ f _) cong$ a = f a

data _≡→_ : Relation (A Congruent→ B) where
    fequiv : { f g : A Congruent→ B } → (∀ {a1 a2 : A} → a1 ≅ a2 → f cong$ a1 ≅ g cong$ a2) → f ≡→ g

private
    ≡→-reflexive : Reflexive _≡→_
    ≡→-reflexive (cong→ f cong) = fequiv (λ a1≅a2 → cong a1≅a2)

    ≡→-symmetric : Symmetric _≡→_
    ≡→-symmetric (fequiv eq) = fequiv (λ a1≅a2 → symmetric-on B (eq (symmetric-on A a1≅a2)))

    ≡→-transitive : Transitive _≡→_
    ≡→-transitive (fequiv {f} {g} feqg) (fequiv {g} {h} geqh) = fequiv (λ {a1} {a2} a1≅a2 → begin≅
        f cong$ a1      ≅< feqg a1≅a2 >
        g cong$ a2      ≅< geqh (reflexive-on A a2) >
        h cong$ a2      ∎)

instance 
    ≡→-IsReflexive : IsReflexive _≡→_
    ≡→-IsReflexive = record { reflexive = ≡→-reflexive }

    ≡→-IsSymmetric : IsSymmetric _≡→_
    ≡→-IsSymmetric = record { symmetric = ≡→-symmetric }

    ≡→-IsTransitive : IsTransitive _≡→_
    ≡→-IsTransitive = record { transitive = ≡→-transitive }

    ≡→-Equivalence : Equivalence _≡→_
    ≡→-Equivalence = record {}
    