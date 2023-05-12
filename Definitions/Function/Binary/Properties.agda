module Definitions.Function.Binary.Properties where

open import Agda.Primitive
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Relation.Equivalence

open Setoid {{...}}
open Equivalence {{...}}

LeftCongruent : { ℓA ℓB ℓC : Level } {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{Setoid A}} → {{Setoid B}} → {{Setoid C}} → (A → B → C) → Set (ℓA ⊔ ℓB ⊔ ℓC)
LeftCongruent _∙_ = ∀ {a} → Congruent (a ∙_)

RightCongruent : { ℓA ℓB ℓC : Level } {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{Setoid A}} → {{Setoid B}} → {{Setoid C}} → (A → B → C) → Set (ℓA ⊔ ℓB ⊔ ℓC)
RightCongruent _∙_ = ∀ {b} → Congruent (_∙ b)

record BiCongruent { ℓA ℓB ℓC : Level } {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {{SA : Setoid A}} {{SB : Setoid B}} {{SC : Setoid C}} (_∙_ : A → B → C) : Set (ℓA ⊔ ℓB ⊔ ℓC) where
    field
        left-congruent : LeftCongruent _∙_
        right-congruent : RightCongruent _∙_

open BiCongruent{{...}}

bi-congruent : { ℓA ℓB ℓC : Level } {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid A}} → {{SB : Setoid B}} → {{SC : Setoid C}} → (_∙_ : A → B → C) → {{BiCongruent _∙_}} → 
    {a1 a2 : A} → a1 ≈ a2 → {b1 b2 : B} → b1 ≈ b2 → (a1 ∙ b1) ≈ (a2 ∙ b2)
bi-congruent _∙_ {a1} {a2} a1≈a2 {b1} {b2} b1≈b2 = begin≈
    a1 ∙ b1     ≈< left-congruent b1≈b2 >
    a1 ∙ b2     ≈< right-congruent a1≈a2 >
    a2 ∙ b2     ∎ 

left-congruent-on : { ℓA ℓB ℓC : Level } {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid A}} → {{SB : Setoid B}} → {{SC : Setoid C}} → 
    (_∙_ : A → B → C) → {{BiCongruent _∙_}} → LeftCongruent _∙_
left-congruent-on _ = left-congruent

right-congruent-on : { ℓA ℓB ℓC : Level } {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid A}} → {{SB : Setoid B}} → {{SC : Setoid C}} → 
    (_∙_ : A → B → C) → {{BiCongruent _∙_}} → RightCongruent _∙_
right-congruent-on _ = right-congruent


Commute : { ℓA ℓB : Level } {A : Set ℓA} {B : Set ℓB} → {{Setoid B}} → (A → A → B) → Set (ℓA ⊔ ℓB)
Commute _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x) 

record IsCommutative { ℓA ℓB : Level } { A : Set ℓA } {B : Set ℓB} {{ SB : Setoid B }} (_∙_ : A → A → B) : Set (ℓA ⊔ ℓB) where
    field
        commute : Commute _∙_

open IsCommutative {{...}}

commute-on : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → {{SB : Setoid B}} → (_∙_ : A → A → B) → {{IC : IsCommutative _∙_}} → Commute _∙_
commute-on _ = commute

private
    commute-congruent : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid A}} → {{SC : Setoid B}} → {_∙_ : A → A → B} → {{IsCommutative _∙_}} → LeftCongruent _∙_ → RightCongruent _∙_
    commute-congruent {_} {_} {_} {_} {_∙_} left-cong {b} {a1} {a2} a1≈a2 = begin≈
        a1 ∙ b      ≈< commute-on _∙_ a1 b >
        b ∙ a1      ≈< left-cong a1≈a2 >
        b ∙ a2      ≈< commute-on _∙_ b a2 >
        a2 ∙ b      ∎

bi-congruent-commutative : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid A}} → {{SC : Setoid B}} → (_∙_ : A → A → B) → {{IsCommutative _∙_}} → LeftCongruent _∙_ → BiCongruent _∙_
bi-congruent-commutative _∙_ left-cong = record {left-congruent = left-cong; right-congruent = commute-congruent left-cong}

Associate : { ℓ : Level } { A : Set ℓ } → {{Setoid A}} → BinOp A → Set ℓ
Associate _∙_ = ∀ x y z → (x ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ z)

record IsAssociative {ℓ : Level} {A : Set ℓ} {{SA : Setoid A}} (_∙_ : BinOp A) : Set ℓ where
    field
        associate : Associate _∙_

open IsAssociative {{...}}

associate-on : {ℓ : Level} → {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → {{IsAssociative _∙_}} → Associate _∙_
associate-on _ = associate

LeftIdentity : {ℓ : Level} {A : Set ℓ} → {{Setoid A}} → BinOp A → A → Set ℓ
LeftIdentity _∙_ i = ∀ x → i ∙ x ≈ x

RightIdentity : {ℓ : Level} {A : Set ℓ} → {{Setoid A}} → BinOp A → A → Set ℓ
RightIdentity _∙_ i = ∀ x → x ∙ i ≈ x

record HasIdentity {ℓ : Level} {A : Set ℓ} {{SA : Setoid A}} (_∙_ : BinOp A) (i : A) : Set ℓ where
    field
        left-identity : LeftIdentity _∙_ i
        right-identity : RightIdentity _∙_ i

open HasIdentity {{...}}

left-identity-on : {ℓ : Level} → {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → LeftIdentity _∙_ i
left-identity-on _ = left-identity

right-identity-on : {ℓ : Level} → {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → RightIdentity _∙_ i
right-identity-on _ = right-identity

private
    commute-identity : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → {_∙_ : BinOp A} {i : A} → {{C : IsCommutative _∙_}} → LeftIdentity _∙_ i → RightIdentity _∙_ i
    commute-identity {_} {_} {{_}} {_∙_} {i} left-id x = begin≈
        x ∙ i   ≈< commute-on _∙_ x i >
        i ∙ x   ≈< left-id x >
        x       ∎

has-identity-commute : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → {_∙_ : BinOp A} → {i : A} → {{C : IsCommutative _∙_}} → LeftIdentity _∙_ i → HasIdentity _∙_ i
has-identity-commute left-id = record {left-identity = left-id; right-identity = commute-identity left-id }

left-id-on : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → LeftIdentity _∙_ i
left-id-on _ = left-identity

right-id-on : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → RightIdentity _∙_ i
right-id-on _ = right-identity

LeftZero : {ℓZ ℓA : Level} {Z : Set ℓZ} {A : Set ℓA} → {{Setoid Z}} → (Z → A → Z) → Z → Set (ℓZ ⊔ ℓA)
LeftZero _∙_ z = ∀ x → z ∙ x ≈ z

RightZero : {ℓA ℓZ : Level} {A : Set ℓA} {Z : Set ℓZ} → {{Setoid Z}} → (A → Z → Z) → Z → Set (ℓZ ⊔ ℓA)
RightZero _∙_ z = ∀ x → x ∙ z ≈ z

record HasZero {ℓ : Level} {A : Set ℓ} {{SA : Setoid A}} (_∙_ : BinOp A) (z : A) : Set ℓ where
    field
        left-zero : LeftZero _∙_ z
        right-zero : RightZero _∙_ z

LeftInverse : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → (id : A) → {{HasIdentity _∙_ id}} → (A → A) → Set ℓ
LeftInverse _∙_ i inv = ∀ x → inv x ∙ x ≈ i

RightInverse : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (_∙_ : BinOp A) → (id : A) → {{HasIdentity _∙_ id}} → (A → A) → Set ℓ
RightInverse _∙_ i inv = ∀ x → x ∙ inv x ≈ i

record HasInverse {ℓ : Level} {A : Set ℓ} {{SA : Setoid A}} (_∙_ : BinOp A) (i : A) (_⁻¹ : A → A) : Set ℓ where
    field
        overlap {{has-identity}} : HasIdentity _∙_ i
        left-inverse : LeftInverse _∙_ i _⁻¹
        right-inverse : RightInverse _∙_ i _⁻¹

private
    commute-inverse : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → {_∙_ : BinOp A} {i : A} {_⁻¹ : A → A} → {{C : IsCommutative _∙_}} → {{HI : HasIdentity _∙_ i}} → 
        LeftInverse _∙_ i _⁻¹ → RightInverse _∙_ i _⁻¹
    commute-inverse {_} {_} {{_}} {_∙_} {i} {inv} left-inv x = begin≈
        x ∙ inv x   ≈< commute-on _∙_ x (inv x) >
        inv x ∙ x   ≈< left-inv x >
        i           ∎

has-inverse-commute : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → {_∙_ : BinOp A} {i : A} {_⁻¹ : A → A} → {{C : IsCommutative _∙_}} → {{HI : HasIdentity _∙_ i}} → 
        LeftInverse _∙_ i _⁻¹ → HasInverse _∙_ i _⁻¹
has-inverse-commute left-inv = record { left-inverse = left-inv; right-inverse = commute-inverse left-inv }

record BiInjective {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
    {{SA : Setoid A}} {{SB : Setoid B}} {{SC : Setoid C}}
    (_∙_ : A → B → C) : Set (ℓA ⊔ ℓB ⊔ ℓC) where
    field
        left-injective : (a : A) → Injective (a ∙_)
        right-injective : (b : B) → Injective (_∙ b)

open BiInjective {{...}}

left-injective-on : {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
     {{SA : Setoid A}} → {{SB : Setoid B}} → {{SC : Setoid C}} →
     (_∙_ : A → B → C) → {{BI : BiInjective _∙_}} → (a : A) → Injective (a ∙_)
left-injective-on _ = left-injective

right-injective-on : {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
     {{SA : Setoid A}} → {{SB : Setoid B}} → {{SC : Setoid C}} →
     (_∙_ : A → B → C) → {{BI : BiInjective _∙_}} → (b : B) → Injective (_∙ b)
right-injective-on _ = right-injective
