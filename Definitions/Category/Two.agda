module Definitions.Category.Two where

open import Agda.Primitive
open import Definitions.Category

data TwoOb : Set where
    source : TwoOb
    target : TwoOb

open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence.Structural.Properties TwoOb

data _⟶_ : TwoOb → TwoOb → Set where
    id-arr : (a : TwoOb) → a ⟶ a 
    the-arr : source ⟶ target

private
    _∘_ : {a b c : TwoOb} → b ⟶ c → a ⟶ b → a ⟶ c
    id-arr _ ∘ arrow = arrow
    arrow ∘ id-arr _ = arrow

    left-congruent-arrow : {a1 a2 b : TwoOb} → a1 ≡ a2 → a1 ⟶ b → a2 ⟶ b
    left-congruent-arrow refl arr = arr

    right-congruent-arrow : {a b1 b2 : TwoOb} → b1 ≡ b2 → a ⟶ b1 → a ⟶ b2
    right-congruent-arrow refl arr = arr

    _=Arrow_ : {a b : TwoOb} → Rel lzero (a ⟶ b)
    _=Arrow_ = _≡_

    =Arrow-equivalence : {a b : TwoOb} → Equivalence _≡_
    =Arrow-equivalence {a} {b} = equiv where
        open import Definitions.Relation.Equivalence.Structural.Properties (a ⟶ b) renaming (≡-Equivalence to equiv)
    
    right-identity-law : {a b : TwoOb} → (f : a ⟶ b) → (f ∘ id-arr a) ≡ f
    right-identity-law (id-arr a) = refl
    right-identity-law the-arr = refl

    associative-law : {a b c d : TwoOb} → (h : c ⟶ d) → (g : b ⟶ c) → (f : a ⟶ b) → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
    associative-law the-arr (id-arr _) (id-arr _) = refl
    associative-law (id-arr _) the-arr (id-arr _) = refl
    associative-law (id-arr _) (id-arr _) the-arr = refl
    associative-law (id-arr a) (id-arr a) (id-arr a) = refl

    =Arrow-left-congruence : {a1 a2 b : TwoOb} → (a1=a2 : a1 ≡ a2) → {ab1 ab2 : a1 ⟶ b} → ab1 ≡ ab2 → left-congruent-arrow a1=a2 ab1 ≡ left-congruent-arrow a1=a2 ab2
    =Arrow-left-congruence refl refl = refl

    =Arrow-right-congruence : {a b1 b2 : TwoOb} → (b1=b2 : b1 ≡ b2) → {ab1 ab2 : a ⟶ b1} → ab1 ≡ ab2 → right-congruent-arrow b1=b2 ab1 ≡ right-congruent-arrow b1=b2 ab2
    =Arrow-right-congruence refl refl = refl

    right-congruent-compose : {a b c : TwoOb} → {bc1 bc2 : b ⟶ c} → bc1 ≡ bc2 → (ab : a ⟶ b) → (bc1 ∘ ab) ≡ (bc2 ∘ ab)
    right-congruent-compose refl _ = refl

    left-congruent-compose : {a b c : TwoOb} → {ab1 ab2 : a ⟶ b} → ab1 ≡ ab2 → (bc : b ⟶ c) → (bc ∘ ab1) ≡ (bc ∘ ab2)
    left-congruent-compose refl _ = refl
    

instance
    two-category : Category TwoOb _⟶_
    two-category = record {
        _∘_ = _∘_;
        left-congruent-arrow = left-congruent-arrow;
        right-congruent-arrow = right-congruent-arrow;
        _=Arrow_ = _≡_;
        =Arrow-equivalence = =Arrow-equivalence;
        identity-arrow = id-arr;
        left-identity-law = λ _ → refl;
        right-identity-law = right-identity-law;
        associative-law = associative-law;
        =Arrow-left-congruence = =Arrow-left-congruence;
        =Arrow-right-congruence = =Arrow-right-congruence;
        left-congruent-compose = left-congruent-compose;
        right-congruent-compose = right-congruent-compose}