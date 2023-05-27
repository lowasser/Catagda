module Function.Unary.Isomorphism where

open import Agda.Primitive
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Relation
open import Relation.Properties
open import Function.Unary.Properties
open import Definitions.DependentPair

open Setoid{{...}}
open Equivalence{{...}}
open IsReflexive{{...}}
open IsTransitive{{...}}
open IsSymmetric{{...}}

private
    variable
        ℓA ℓB ℓ=A : Level

record Iso {A : Set ℓA} {B : Set ℓB} {{SA : Setoid ℓ=A A}} (f : A → B) (g : B → A) : Set (ℓA ⊔ ℓB ⊔ ℓ=A) where
    field
        inverse-law : (a : A) → g (f a) ≅ a

open Iso {{...}}

data _induced-≅_ {A : Set ℓA} {B : Set ℓB} {{SA : Setoid ℓ=A A}} {f : A → B} {g : B → A} (iso : Iso f g) : Rel (ℓA ⊔ ℓB ⊔ ℓ=A) B where
    induced-≅ : {b1 b2 : B} → g b1 ≅ g b2 → _induced-≅_ iso b1 b2

private
    induced-≅-reflexive : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → Reflexive (_induced-≅_ iso)
    induced-≅-reflexive {_} {_} {_} {_} {_} {_} {g} iso b = induced-≅ (reflexive (g b))

    induced-≅-transitive : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → Transitive (_induced-≅_ iso)
    induced-≅-transitive _ (induced-≅ ga≅gb) (induced-≅ gb≅gc) = induced-≅ (transitive ga≅gb gb≅gc)

    induced-≅-symmetric : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → Symmetric (_induced-≅_ iso)
    induced-≅-symmetric _ (induced-≅ ga≅gb) = induced-≅ (symmetric ga≅gb)

induced-≅-is-reflexive : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → IsReflexive (_induced-≅_ iso)
induced-≅-is-reflexive iso = record { reflexive = induced-≅-reflexive iso }

induced-≅-is-transitive : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → IsTransitive (_induced-≅_ iso)
induced-≅-is-transitive iso = record { transitive = induced-≅-transitive iso }

induced-≅-preorder : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → PreOrder (_induced-≅_ iso)
induced-≅-preorder iso = record { is-transitive = induced-≅-is-transitive iso; is-reflexive = induced-≅-is-reflexive iso }

induced-≅-is-symmetric : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → IsSymmetric (_induced-≅_ iso)
induced-≅-is-symmetric iso = record { symmetric = induced-≅-symmetric iso }

induced-≅-equivalence : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → Equivalence (_induced-≅_ iso)
induced-≅-equivalence iso = record { preorder = induced-≅-preorder iso; is-symmetric = induced-≅-is-symmetric iso}

induced-≅-setoid : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → Setoid (ℓA ⊔ ℓB ⊔ ℓ=A) B
induced-≅-setoid iso = record { _≅_ = _induced-≅_ iso; equivalence = induced-≅-equivalence iso}

iso-inverse-inverse-law : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} → {g : B → A} → (iso : Iso f g) → (b : B) → _induced-≅_ iso (f (g b)) b
iso-inverse-inverse-law {_} {_} {_} {_} {_} {f} {g} iso b = induced-≅ (begin≅
    g (f (g b))         ≅< Iso.inverse-law iso (g b) >
    g b                 ∎)

iso-inverse : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} → {g : B → A} → (iso : Iso f g) → Iso {{induced-≅-setoid iso}} g f
iso-inverse iso = record { inverse-law = iso-inverse-inverse-law iso }

iso-inverse-congruent : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → {{IsCongruent f {{SA}} {{induced-≅-setoid iso}}}} →
    Congruent g {{induced-≅-setoid iso}} {{SA}}
iso-inverse-congruent iso (induced-≅ a1≅a2) = a1≅a2

iso-injective : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → {{IsCongruent f {{SA}} {{induced-≅-setoid iso}}}} →
    Injective f {{SA}} {{induced-≅-setoid iso}}
iso-injective {_} {_} {_} {_} {_} {f} {g} iso {a1} {a2} (induced-≅ gfa1≅gfa2) = begin≅
        a1          ≅< symmetric (Iso.inverse-law iso a1) >
        g (f a1)    ≅< gfa1≅gfa2 >
        g (f a2)    ≅< Iso.inverse-law iso a2 >
        a2          ∎

iso-surjective : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {f : A → B} {g : B → A} → (iso : Iso f g) → Surjective f {{induced-≅-setoid iso}}
iso-surjective {_} {_} {_} {_} {_} {_} {g} iso b = (g b , iso-inverse-inverse-law iso b)