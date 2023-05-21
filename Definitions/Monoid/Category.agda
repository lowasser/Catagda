open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Monoid
open import Definitions.Function.Binary

module Definitions.Monoid.Category {ℓ ℓ= : Level} {A : Set ℓ} {{SA : Setoid ℓ= A}} (_∙_ : BinOp A) {id : A} {{M : Monoid _∙_ id}} where

open import Definitions.Category
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Function.Binary.Properties

open Setoid {{...}}

data Object : Set where
    ob : Object

open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence.Structural.Properties (Object)

data Morphism : Object → Object → Set ℓ where
    morph : (a : A) → Morphism ob ob

data _=m=_ : {m n : Object} → Rel (ℓ= ⊔ ℓ) (Morphism m n) where
    meq : {a b : A} → a ≅ b → morph a =m= morph b

open Monoid {{...}}
open HasIdentity {{...}}

private
    _∘_ : {a b c : Object} → Morphism b c → Morphism a b → Morphism a c
    morph a ∘ morph b = morph (a ∙ b)

    id-morph : (a : Object) → Morphism a a
    id-morph ob = morph id

    left-cong : {a1 a2 b : Object} → a1 ≡ a2 → Morphism a1 b → Morphism a2 b
    left-cong {ob} {ob} _ (morph m) = morph m
    
    right-cong : {a b1 b2 : Object} → b1 ≡ b2 → Morphism a b1 → Morphism a b2
    right-cong {_} {ob} {ob} _ (morph m) = morph m

    =m=-reflexive : {a b : Object} → Reflexive (_=m=_ {a} {b})
    =m=-reflexive (morph m) = meq (reflexive-on A m)

    =m=-symmetric : {a b : Object} → Symmetric (_=m=_ {a} {b})
    =m=-symmetric (meq a=b) = meq (symmetric-on A a=b)

    =m=-transitive : {a b : Object} → Transitive (_=m=_ {a} {b})
    =m=-transitive (meq a=b) (meq b=c) = meq (transitive-on A a=b b=c)

    left-id-law : {a b : Object} → (f : Morphism a b) → (id-morph b ∘ f) =m= f
    left-id-law (morph f) = meq (left-identity-on _∙_ f)

    right-id-law : {a b : Object} → (f : Morphism a b) → (f ∘ id-morph a) =m= f
    right-id-law (morph f) = meq (right-identity-on _∙_ f)
    -- TODO: more isomorphism things, ideally, and generalize congruence

    associative-law : {a b c d : Object} → (h : Morphism c d) → (g : Morphism b c) → (f : Morphism a b) → (h ∘ (g ∘ f)) =m= ((h ∘ g) ∘ f)
    associative-law (morph h) (morph g) (morph f) = meq (associate-on _∙_ h g f)

    left-cong-arrow : {a1 a2 b : Object} → (a1=a2 : a1 ≡ a2) → {ab1 ab2 : Morphism a1 b} → ab1 =m= ab2 → left-cong a1=a2 ab1 =m= left-cong a1=a2 ab2
    left-cong-arrow refl (meq eq12) = meq eq12
    
    right-cong-arrow : {a1 a2 b : Object} → (a1=a2 : a1 ≡ a2) → {ab1 ab2 : Morphism b a1} → ab1 =m= ab2 → right-cong a1=a2 ab1 =m= right-cong a1=a2 ab2
    right-cong-arrow refl (meq eq12) = meq eq12

instance
    monoid-category : Category Object Morphism
    monoid-category = record {
        _∘_ = _∘_;
        _=→_ = _=m=_ ;
        identity-arrow = id-morph;
        left-congruent-arrow = left-cong;
        right-congruent-arrow = right-cong;
        =→-equivalence = λ {a} {b} → make-equivalence (_=m=_ {a} {b}) (=m=-reflexive {a} {b}) (=m=-transitive {a} {b}) (=m=-symmetric {a} {b});
        left-identity-law = left-id-law;
        right-identity-law = right-id-law;
        associative-law = associative-law;
        =→-left-congruence = left-cong-arrow;
        =→-right-congruence = right-cong-arrow}