open import Agda.Primitive

module Definitions.Category.Cat (ℓ : Level) where

open import Definitions.Category
open import Definitions.Setoid
open import Definitions.Function.Properties
open import Definitions.Relation.Properties

record CatOb : Set (lsuc ℓ) where
    field
        objects : Set ℓ
        arrow : objects → objects → Set ℓ
        {{objects-setoid}} : Setoid ℓ objects

        category : Category {ℓ} {ℓ} {ℓ} {ℓ} objects arrow

open CatOb
open Category
open Equivalence {{...}}
open PreOrder {{...}}
open IsTransitive {{...}}
open IsSymmetric {{...}}
open IsReflexive {{...}}

record Functor (A : CatOb) (B : CatOb) : Set ℓ where
    field
        map-ob : objects A Congruent→ objects B
        map-arrow : {a1 a2 : objects A} → arrow A a1 a2 → arrow B (map-ob cong$ a1) (map-ob cong$ a2)
        map-arrow-congruent : {a1 a2 : objects A} → {arr1 arr2 : arrow A a1 a2} → _=Arrow_ (category A) arr1 arr2 → _=Arrow_ (category B) (map-arrow arr1) (map-arrow arr2)

        identity-to-identity : (a : objects A) → _=Arrow_ (category B) (map-arrow (identity-arrow (category A) a)) (identity-arrow (category B) (map-ob cong$ a))
        compose-to-compose : {x y z : objects A} → (f : arrow A y z) → (g : arrow A x y) → 
            _=Arrow_ (category B) (map-arrow (_∘_ (category A) f g)) (_∘_ (category B) (map-arrow f) (map-arrow g))

open Functor

private 
    id-to-id-compose : {A B C : CatOb} → (f : Functor B C) → (g : Functor A B) → (a : objects A) → 
            _=Arrow_ (category C) (map-arrow f (map-arrow g (identity-arrow (category A) a))) (identity-arrow (category C) ((map-ob f cong∘ map-ob g) cong$ a))
    id-to-id-compose {A} {B} {C} f g a = transitive-equivalence 
        (=Arrow-equivalence (category C))
        (map-arrow-congruent f (identity-to-identity g a))
        (identity-to-identity f (map-ob g cong$ a))

    comp-to-comp : {A B C : CatOb} → (f : Functor B C) → (g : Functor A B) → {x y z : objects A} → (a1 : arrow A y z) → (a2 : arrow A x y) → 
        _=Arrow_ (category C) (map-arrow f (map-arrow g (_∘_ (category A) a1 a2))) (_∘_ (category C) (map-arrow f (map-arrow g a1)) (map-arrow f (map-arrow g a2)))
    comp-to-comp {A} {B} {C} f g a1 a2 = transitive-equivalence
        (=Arrow-equivalence (category C))
        (map-arrow-congruent f (compose-to-compose g a1 a2))
        (compose-to-compose f (map-arrow g a1) (map-arrow g a2))

_∘Functor_ : {A B C : CatOb} → Functor B C → Functor A B → Functor A C
_∘Functor_ {A} {B} {C} f g = record {
        map-ob = map-ob f cong∘ map-ob g;
        map-arrow = λ arr → map-arrow f (map-arrow g arr);
        map-arrow-congruent = λ arr1=arr2 → map-arrow-congruent f (map-arrow-congruent g arr1=arr2);
        identity-to-identity = id-to-id-compose f g;
        compose-to-compose = comp-to-comp f g}