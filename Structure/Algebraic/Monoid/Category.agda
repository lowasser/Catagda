open import Agda.Primitive
open import Structure.Setoid
open import Structure.Algebraic.Monoid
open import Function.Binary

module Structure.Algebraic.Monoid.Category {ℓ ℓ= : Level} {A : Set ℓ} {{SA : Setoid ℓ= A}} (_∙_ : BinOp A) {id : A} {{M : Monoid _∙_ id}} where

open import Agda.Builtin.Unit
open import Structure.Category
open import Relation
open import Relation.Properties
open import Function.Binary.Properties

open Setoid {{...}}

open import Relation.Equivalence.Structural
open import Relation.Equivalence.Structural.Properties (⊤)

data Morphism : ⊤ → ⊤ → Set ℓ where
    morph : (a : A) → Morphism tt tt

data _=m=_ : {m n : ⊤} → Rel (ℓ= ⊔ ℓ) (Morphism m n) where
    meq : {a b : A} → a ≅ b → morph a =m= morph b

open Monoid {{...}}
open HasIdentity {{...}}

private
    _∘_ : {a b c : ⊤} → Morphism b c → Morphism a b → Morphism a c
    morph a ∘ morph b = morph (a ∙ b)

    id-morph : (a : ⊤) → Morphism a a
    id-morph tt = morph id

    left-cong : {a1 a2 b : ⊤} → a1 ≡ a2 → Morphism a1 b → Morphism a2 b
    left-cong {tt} {tt} _ (morph m) = morph m
    
    right-cong : {a b1 b2 : ⊤} → b1 ≡ b2 → Morphism a b1 → Morphism a b2
    right-cong {_} {tt} {tt} _ (morph m) = morph m

    =m=-reflexive : {a b : ⊤} → Reflexive (_=m=_ {a} {b})
    =m=-reflexive (morph m) = meq (reflexive-on A m)

    =m=-symmetric : {a b : ⊤} → Symmetric (_=m=_ {a} {b})
    =m=-symmetric (meq a=b) = meq (symmetric-on A a=b)

    =m=-transitive : {a b : ⊤} → Transitive (_=m=_ {a} {b})
    =m=-transitive (meq a=b) (meq b=c) = meq (transitive-on A a=b b=c)

    left-id-law : {a b : ⊤} → (f : Morphism a b) → (id-morph b ∘ f) =m= f
    left-id-law (morph f) = meq (left-identity-on _∙_ f)

    right-id-law : {a b : ⊤} → (f : Morphism a b) → (f ∘ id-morph a) =m= f
    right-id-law (morph f) = meq (right-identity-on _∙_ f)

    associative-law : {a b c d : ⊤} → (h : Morphism c d) → (g : Morphism b c) → (f : Morphism a b) → (h ∘ (g ∘ f)) =m= ((h ∘ g) ∘ f)
    associative-law (morph h) (morph g) (morph f) = meq (left-associate-on _∙_ h g f)

    left-cong-arrow : {a1 a2 b : ⊤} → (a1=a2 : a1 ≡ a2) → {ab1 ab2 : Morphism a1 b} → ab1 =m= ab2 → left-cong a1=a2 ab1 =m= left-cong a1=a2 ab2
    left-cong-arrow refl (meq eq12) = meq eq12
    
    right-cong-arrow : {a1 a2 b : ⊤} → (a1=a2 : a1 ≡ a2) → {ab1 ab2 : Morphism b a1} → ab1 =m= ab2 → right-cong a1=a2 ab1 =m= right-cong a1=a2 ab2
    right-cong-arrow refl (meq eq12) = meq eq12

    right-congruent-compose : {a b c : ⊤} {bc1 bc2 : Morphism b c} → bc1 =m= bc2 → (ab : Morphism a b) → (bc1 ∘ ab) =m= (bc2 ∘ ab)
    right-congruent-compose (meq f=g) (morph _) = meq (right-congruent-on _∙_ f=g)

    left-congruent-compose : {a b c : ⊤} {ab1 ab2 : Morphism a b} → ab1 =m= ab2 → (bc : Morphism b c) → (bc ∘ ab1) =m= (bc ∘ ab2)
    left-congruent-compose (meq f=g) (morph _) = meq (left-congruent-on _∙_ f=g)

instance
    monoid-category : Category ⊤ Morphism
    monoid-category = record {
        _∘_ = _∘_;
        _=Arrow_ = _=m=_ ;
        identity-arrow = id-morph;
        left-congruent-arrow = left-cong;
        right-congruent-arrow = right-cong;
        =Arrow-equivalence = λ {a} {b} → make-equivalence (_=m=_ {a} {b}) (=m=-reflexive {a} {b}) (=m=-transitive {a} {b}) (=m=-symmetric {a} {b});
        left-identity-law = left-id-law;
        right-identity-law = right-id-law;
        associative-law = associative-law;
        =Arrow-left-congruence = left-cong-arrow;
        =Arrow-right-congruence = right-cong-arrow;
        right-congruent-compose = right-congruent-compose;
        left-congruent-compose = left-congruent-compose} 