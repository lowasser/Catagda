open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Monoid
open import Definitions.Function.Binary

module Definitions.Monoid.Category {ℓ : Level} {A : Set ℓ} (_∙_ : BinOp A) {id : A} {{M : Monoid _∙_ id}} where

open import Definitions.Category
open import Definitions.Relation
open import Definitions.Relation.Properties

open Setoid {{...}}

data Object : Set where
    ob : Object

open import Definitions.Relation.Equivalence.AllEqual (Object)

data Morphism : Object → Object → Set ℓ where
    morph : (a : A) → Morphism ob ob

data _=m=_ : {m n : Object} → Relation (Morphism m n) where
    meq : {a b : A} → a ≈ b → morph a =m= morph b

private
    _∘_ : {a b c : Object} → Morphism b c → Morphism a b → Morphism a c
    morph a ∘ morph b = morph (a ∙ b)

    id-morph : (a : Object) → Morphism a a
    id-morph ob = morph id

    left-cong : {a1 a2 b : Object} → a1 == a2 → Morphism a1 b → Morphism a2 b
    left-cong {ob} {ob} _ (morph m) = morph m
    
    right-cong : {a b1 b2 : Object} → b1 == b2 → Morphism a b1 → Morphism a b2
    right-cong {_} {ob} {ob} _ (morph m) = morph m

    =m=-reflexive : {a b : Object} → Reflexive (_=m=_ {a} {b})
    =m=-reflexive (morph m) = meq (reflexive-on A m)

    -- TODO: more isomorphism things, ideally, and generalize congruence

instance
    monoid-category : Category Object Morphism
    monoid-category = record {
        _∘_ = _∘_;
        _=→_ = _=m=_ ;
        identity-arrow = id-morph;
        left-congruent-arrow = left-cong;
        right-congruent-arrow = right-cong
        }