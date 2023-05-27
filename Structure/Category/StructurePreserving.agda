open import Agda.Primitive
open import Structure.Setoid
open import Relation
open import Function.Properties
open import Relation.Equivalence.Structural
open import Relation.Properties
open import Structure.Category

module Structure.Category.StructurePreserving 
    {ℓ : Level} 
    (Ob : Set (lsuc ℓ))
    (ob-elements : Ob → Set ℓ)
    (ob-setoid : (ob : Ob) → Setoid ℓ (ob-elements ob))
    (Morph : Ob → Ob → Set (lsuc ℓ))
    (morph-fn : {a b : Ob} → Morph a b → _Congruent→_ (ob-elements a) (ob-elements b) {{ob-setoid a}} {{ob-setoid b}})
    (id-morph : (a : Ob) → Morph a a)
    (id-morph-is-id-function : (a : Ob) → morph-fn (id-morph a) ≡ id-congruent (ob-elements a) {{ob-setoid a}})
    (morph-composition : {a b c : Ob} → Morph b c → Morph a b → Morph a c)
    (composition-composes : {a b c : Ob} → (f : Morph b c) → (g : Morph a b) → morph-fn (morph-composition f g) ≡ _cong∘_ {{ob-setoid a}} {{ob-setoid b}} {{ob-setoid c}} (morph-fn f) (morph-fn g))
    where

open import Structure.Setoid.Equation
open _Congruent→_
open import Relation.Equivalence.Structural.Properties Ob renaming (≡-Setoid to setoid-of-obs)

data =Morphism (A B : Ob) : Rel (lsuc ℓ) (Morph A B) where
    =-morphism : {f g : Morph A B} → Pointwise= (ob-elements A) (ob-elements B) {{ob-setoid A}} {{ob-setoid B}} (morph-fn f) (morph-fn g) → =Morphism A B f g

private
    left-identity-law : {A B : Ob} → (f : Morph A B) → =Morphism A B (morph-composition (id-morph B) f) f
    left-identity-law {A} {B} f = =-morphism (fequiv (morph-fn (morph-composition (id-morph B) f)) (morph-fn f) (λ a → begin≅
        morph-fn (morph-composition (id-morph B) f) cong$ a     ≡< ≡-cong (_cong$ a) (composition-composes (id-morph B) f) >
        (morph-fn (id-morph B) cong∘ morph-fn f) cong$ a        ≡< ≡-cong (λ k → (k cong∘ morph-fn f) cong$ a) (id-morph-is-id-function B) >
        (id-congruent (ob-elements B) cong∘ morph-fn f) cong$ a ≅<>
        (cong-func (id-congruent (ob-elements B))) (cong-func (morph-fn f) a)
                                                                ≅<>
        cong-func (morph-fn f) a                                ∎))
        where   instance
                    b-setoid = ob-setoid B
                    a-setoid = ob-setoid A
                    
    right-identity-law : {A B : Ob} → (f : Morph A B) → =Morphism A B (morph-composition f (id-morph A)) f
    right-identity-law {A} {B} f = =-morphism (fequiv (morph-fn (morph-composition f (id-morph A))) (morph-fn f) (λ a → begin≅ 
        morph-fn (morph-composition f (id-morph A)) cong$ a     ≡< ≡-cong (_cong$ a) (composition-composes f (id-morph A)) >
        (morph-fn f cong∘ morph-fn (id-morph A)) cong$ a        ≡< ≡-cong (λ k → (morph-fn f cong∘ k) cong$ a) (id-morph-is-id-function A) >
        (morph-fn f cong∘ id-congruent (ob-elements A)) cong$ a ≅<>
        (cong-func (morph-fn f)) (cong-func (id-congruent (ob-elements A)) a)
                                                                ≅<>
        cong-func (morph-fn f) a                                ∎))
        where   instance
                    b-setoid = ob-setoid B
                    a-setoid = ob-setoid A

    associative-law : {A B C D : Ob} → (h : Morph C D) → (g : Morph B C) → (f : Morph A B) → =Morphism A D (morph-composition h (morph-composition g f)) (morph-composition (morph-composition h g) f)
    associative-law {A} {B} {C} {D} h g f = =-morphism (fequiv (morph-fn (morph-composition h (morph-composition g f))) (morph-fn (morph-composition (morph-composition h g) f)) (λ a → begin≅
        morph-fn (morph-composition h (morph-composition g f)) cong$ a      ≡< ≡-cong (_cong$ a) (composition-composes h (morph-composition g f)) >
        (morph-fn h cong∘ morph-fn (morph-composition g f)) cong$ a         ≡< ≡-cong (λ k → (morph-fn h cong∘ k) cong$ a) (composition-composes g f) >
        (morph-fn h cong∘ (morph-fn g cong∘ morph-fn f)) cong$ a            ≅<>
        cong-func (morph-fn h) (cong-func (morph-fn g) (cong-func (morph-fn f) a)) ≡< ≡-cong (_cong$ (cong-func (morph-fn f) a)) (≡-sym (composition-composes h g)) >
        morph-fn (morph-composition h g) cong$ (cong-func (morph-fn f) a)     ≡< ≡-cong (_cong$ a) (≡-sym (composition-composes (morph-composition h g) f)) >
        morph-fn (morph-composition (morph-composition h g) f) cong$ a            ∎))
        where   instance
                    d-setoid = ob-setoid D
                    c-setoid = ob-setoid C 
                    b-setoid = ob-setoid B
                    a-setoid = ob-setoid A

    =Morph-reflexive : (A B : Ob) → Reflexive (=Morphism A B)
    =Morph-reflexive A B f = =-morphism (fequiv (morph-fn f) (morph-fn f) λ a → reflexive-on (ob-elements B) (morph-fn f cong$ a))
        where instance
                a-setoid = ob-setoid A
                b-setoid = ob-setoid B

    =Morph-symmetric : (A B : Ob) → Symmetric (=Morphism A B)
    =Morph-symmetric A B (=-morphism (fequiv a b a=b)) = =-morphism (fequiv b a (λ a → symmetric-on (ob-elements B) (a=b a)))
        where instance
                a-setoid = ob-setoid A
                b-setoid = ob-setoid B

    =Morph-transitive : (A B : Ob) → Transitive (=Morphism A B)
    =Morph-transitive A B (=-morphism (fequiv a b a=b)) (=-morphism (fequiv b c b=c)) = =-morphism (fequiv a c (λ a → transitive-on (ob-elements B) (a=b a) (b=c a)))
        where instance
                a-setoid = ob-setoid A
                b-setoid = ob-setoid B

    =Morph-equivalence : {A B : Ob} → Equivalence (=Morphism A B)
    =Morph-equivalence {A} {B} = make-equivalence (=Morphism A B) (=Morph-reflexive A B) (=Morph-transitive A B) (=Morph-symmetric A B)

    left-congruent-arrow : {A1 A2 B : Ob} → A1 ≡ A2 → Morph A1 B → Morph A2 B
    left-congruent-arrow refl m = m

    right-congruent-arrow : {A B1 B2 : Ob} → B1 ≡ B2 → Morph A B1 → Morph A B2
    right-congruent-arrow refl m = m

    =Morph-left-congruence : {a1 a2 b : Ob} → (a1=a2 : a1 ≡ a2) → {ab1 ab2 : Morph a1 b} → =Morphism a1 b ab1 ab2 →
            =Morphism a2 b (left-congruent-arrow a1=a2 ab1) (left-congruent-arrow a1=a2 ab2)
    =Morph-left-congruence refl eq = eq

    =Morph-right-congruence : {a b1 b2 : Ob} → (b1=b2 : b1 ≡ b2) → {ab1 ab2 : Morph a b1} → =Morphism a b1 ab1 ab2 →
            =Morphism a b2 (right-congruent-arrow b1=b2 ab1) (right-congruent-arrow b1=b2 ab2)
    =Morph-right-congruence refl eq = eq

    right-congruent-compose : {a b c : Ob} {bc1 bc2 : Morph b c} → =Morphism b c bc1 bc2 → (ab : Morph a b) → =Morphism a c (morph-composition bc1 ab) (morph-composition bc2 ab)
    right-congruent-compose {a} {b} {c} {bc1} {bc2} (=-morphism (fequiv _ _ bc1=bc2)) ab = 
        =-morphism (fequiv (morph-fn (morph-composition bc1 ab)) (morph-fn (morph-composition bc2 ab)) (λ a → begin≅
            (morph-fn (morph-composition bc1 ab)) cong$ a       ≡< ≡-cong (_cong$ a) (composition-composes bc1 ab) >
            (morph-fn bc1 cong∘ morph-fn ab) cong$ a            ≅<>
            morph-fn bc1 cong$ (morph-fn ab cong$ a)            ≅< bc1=bc2 (morph-fn ab cong$ a) >
            morph-fn bc2 cong$ (morph-fn ab cong$ a)            ≅<>
            (morph-fn bc2 cong∘ morph-fn ab) cong$ a            ≡< ≡-cong (_cong$ a) (≡-sym (composition-composes bc2 ab)) >
            morph-fn (morph-composition bc2 ab) cong$ a         ∎))
            where   instance
                        a-setoid = ob-setoid a
                        b-setoid = ob-setoid b
                        c-setoid = ob-setoid c

    left-congruent-compose : {a b c : Ob} {ab1 ab2 : Morph a b} → =Morphism a b ab1 ab2 → (bc : Morph b c) → =Morphism a c (morph-composition bc ab1) (morph-composition bc ab2)
    left-congruent-compose {a} {b} {c} {ab1} {ab2} (=-morphism (fequiv _ _ ab1=ab2)) bc =
        =-morphism (fequiv (morph-fn (morph-composition bc ab1)) (morph-fn (morph-composition bc ab2)) (λ a → begin≅
            morph-fn (morph-composition bc ab1) cong$ a     ≡< ≡-cong (_cong$ a) (composition-composes bc ab1) >
            (morph-fn bc cong∘ morph-fn ab1) cong$ a        ≅<>
            morph-fn bc cong$ (morph-fn ab1 cong$ a)        ≅< is-congruent (morph-fn bc) (ab1=ab2 a) >
            morph-fn bc cong$ (morph-fn ab2 cong$ a)        ≅<>
            (morph-fn bc cong∘ morph-fn ab2) cong$ a        ≡< ≡-cong (_cong$ a) (≡-sym (composition-composes bc ab2)) >
            morph-fn (morph-composition bc ab2) cong$ a     ∎))
            where   instance
                        a-setoid = ob-setoid a
                        b-setoid = ob-setoid b
                        c-setoid = ob-setoid c

instance
    morph-category : Category {lsuc ℓ} {lsuc ℓ} {lsuc ℓ} {lsuc ℓ} Ob Morph
    morph-category = record {
        _∘_ = morph-composition;
        left-congruent-arrow = left-congruent-arrow;
        right-congruent-arrow = right-congruent-arrow;
        _=Arrow_ = λ {A} {B} → =Morphism A B;
        =Arrow-equivalence = =Morph-equivalence;
        identity-arrow = id-morph;
        left-identity-law = left-identity-law;
        right-identity-law = right-identity-law;
        =Arrow-left-congruence = =Morph-left-congruence;
        =Arrow-right-congruence = =Morph-right-congruence;
        associative-law = associative-law;
        right-congruent-compose = right-congruent-compose;
        left-congruent-compose = left-congruent-compose}
 