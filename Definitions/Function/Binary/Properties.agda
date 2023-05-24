module Definitions.Function.Binary.Properties where

open import Agda.Primitive
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Relation
open import Definitions.Relation.Properties

private
    variable
        ℓZ ℓA ℓB ℓC ℓ=Z ℓ=A ℓ=B ℓ=C : Level

open Setoid {{...}}
open Equivalence {{...}}

LeftCongruent : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{Setoid ℓ=B B}} → {{Setoid ℓ=C C}} → (A → B → C) → Set (ℓA ⊔ ℓB ⊔ ℓ=B ⊔ ℓ=C)
LeftCongruent _∙_ = ∀ {a} → Congruent (a ∙_)

RightCongruent : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{Setoid ℓ=A A}} → {{Setoid ℓ=C C}} → (A → B → C) → Set (ℓA ⊔ ℓB ⊔ ℓ=A ⊔ ℓ=C)
RightCongruent _∙_ = ∀ {b} → Congruent (_∙ b)

record BiCongruent  {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} {{SC : Setoid ℓ=C C}} (_∙_ : A → B → C) : Set (ℓA ⊔ ℓB ⊔ ℓC ⊔ ℓ=A ⊔ ℓ=B ⊔ ℓ=C) where
    field
        left-congruent : LeftCongruent _∙_
        right-congruent : RightCongruent _∙_

open BiCongruent{{...}}

bi-congruent : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {{SC : Setoid ℓ=C C}} → (_∙_ : A → B → C) → {{BiCongruent _∙_}} → 
    {a1 a2 : A} → a1 ≅ a2 → {b1 b2 : B} → b1 ≅ b2 → (a1 ∙ b1) ≅ (a2 ∙ b2)
bi-congruent _∙_ {a1} {a2} a1≅a2 {b1} {b2} b1≅b2 = begin≅
    a1 ∙ b1     ≅< left-congruent b1≅b2 >
    a1 ∙ b2     ≅< right-congruent a1≅a2 >
    a2 ∙ b2     ∎ 

left-congruent-on : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {{SC : Setoid ℓ=C C}} → 
    (_∙_ : A → B → C) → {{BiCongruent _∙_}} → LeftCongruent _∙_
left-congruent-on _ = left-congruent

right-congruent-on : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {{SC : Setoid ℓ=C C}} → 
    (_∙_ : A → B → C) → {{BiCongruent _∙_}} → RightCongruent _∙_
right-congruent-on _ = right-congruent


Commute : {A : Set ℓA} {B : Set ℓB} → {{Setoid ℓ=B B}} → (A → A → B) → Set (ℓA ⊔ ℓ=B)
Commute _∙_ = ∀ x y → (x ∙ y) ≅ (y ∙ x) 

record IsCommutative { A : Set ℓA } {B : Set ℓB} {{ SB : Setoid ℓ=B B }} (_∙_ : A → A → B) : Set (ℓA ⊔ ℓ=B) where
    field
        commute : Commute _∙_

open IsCommutative {{...}}

commute-on : {A : Set ℓA} {B : Set ℓB} → {{SB : Setoid ℓ=B B}} → (_∙_ : A → A → B) → {{IC : IsCommutative _∙_}} → Commute _∙_
commute-on _ = commute

private
    commute-congruent : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {_∙_ : A → A → B} → {{IsCommutative _∙_}} → LeftCongruent _∙_ → RightCongruent _∙_
    commute-congruent {_} {_} {_} {_} {_} {_} {_∙_} left-cong {b} {a1} {a2} a1≅a2 = begin≅
        a1 ∙ b      ≅< commute-on _∙_ a1 b >
        b ∙ a1      ≅< left-cong a1≅a2 >
        b ∙ a2      ≅< commute-on _∙_ b a2 >
        a2 ∙ b      ∎

bi-congruent-commutative : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SC : Setoid ℓ=B B}} → (_∙_ : A → A → B) → {{IsCommutative _∙_}} → LeftCongruent _∙_ → BiCongruent _∙_
bi-congruent-commutative _∙_ left-cong = record {left-congruent = left-cong; right-congruent = commute-congruent left-cong}

Associate : { A : Set ℓA } → {{Setoid ℓ=A A}} → BinOp A → Set (ℓA ⊔ ℓ=A)
Associate _∙_ = ∀ x y z → (x ∙ (y ∙ z)) ≅ ((x ∙ y) ∙ z)

record IsAssociative {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_∙_ : BinOp A) : Set (ℓA ⊔ ℓ=A) where
    field
        associate : Associate _∙_

open IsAssociative {{...}}

associate-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {{IsAssociative _∙_}} → Associate _∙_
associate-on _ = associate

left-associate-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {{IsAssociative _∙_}} → Associate _∙_
left-associate-on = associate-on

right-associate-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {{IsAssociative _∙_}} → (a b c : A) → (a ∙ b) ∙ c ≅ a ∙ (b ∙ c)
right-associate-on {_} {_} {A} _∙_ a b c = symmetric-on A (left-associate-on _∙_ a b c)

LeftIdentity : {A : Set ℓA} → {{Setoid ℓ=A A}} → BinOp A → A → Set (ℓA ⊔ ℓ=A)
LeftIdentity _∙_ i = ∀ x → i ∙ x ≅ x

RightIdentity : {A : Set ℓA} → {{Setoid ℓ=A A}} → BinOp A → A → Set (ℓA ⊔ ℓ=A)
RightIdentity _∙_ i = ∀ x → x ∙ i ≅ x

record HasIdentity {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_∙_ : BinOp A) (i : A) : Set (ℓA ⊔ ℓ=A) where
    field
        left-identity : LeftIdentity _∙_ i
        right-identity : RightIdentity _∙_ i

open HasIdentity {{...}}

left-identity-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → LeftIdentity _∙_ i
left-identity-on _ = left-identity

right-identity-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → RightIdentity _∙_ i
right-identity-on _ = right-identity

private
    commute-identity : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → {_∙_ : BinOp A} {i : A} → {{C : IsCommutative _∙_}} → LeftIdentity _∙_ i → RightIdentity _∙_ i
    commute-identity {_} {_} {{_}} {_∙_} {i} left-id x = begin≅
        x ∙ i   ≅< commute-on _∙_ x i >
        i ∙ x   ≅< left-id x >
        x       ∎

has-identity-commute : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → {_∙_ : BinOp A} → {i : A} → {{C : IsCommutative _∙_}} → LeftIdentity _∙_ i → HasIdentity _∙_ i
has-identity-commute left-id = record {left-identity = left-id; right-identity = commute-identity left-id }

left-id-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → LeftIdentity _∙_ i
left-id-on _ = left-identity

right-id-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → {i : A} → {{HasIdentity _∙_ i}} → RightIdentity _∙_ i
right-id-on _ = right-identity

LeftZero : {Z : Set ℓZ} {A : Set ℓA} → {{Setoid ℓ=Z Z}} → (Z → A → Z) → Z → Set (ℓ=Z ⊔ ℓA)
LeftZero _∙_ z = ∀ x → z ∙ x ≅ z

RightZero : {Z : Set ℓZ} {A : Set ℓA} → {{Setoid ℓ=Z Z}} → (A → Z → Z) → Z → Set (ℓ=Z ⊔ ℓA)
RightZero _∙_ z = ∀ x → x ∙ z ≅ z

record HasZero {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_∙_ : BinOp A) (z : A) : Set (ℓA ⊔ ℓ=A) where
    field
        left-zero : LeftZero _∙_ z
        right-zero : RightZero _∙_ z

right-zero-on :{A : Set ℓA} → {{S : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (z : A) → {{HZ : HasZero _∙_ z}} → RightZero _∙_ z
right-zero-on _ _ {{HZ}} = HasZero.right-zero HZ

LeftInverse : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (id : A) → {{HasIdentity _∙_ id}} → (A → A) → Set (ℓA ⊔ ℓ=A)
LeftInverse _∙_ i inv = ∀ x → inv x ∙ x ≅ i

RightInverse : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (id : A) → {{HasIdentity _∙_ id}} → (A → A) → Set (ℓA ⊔ ℓ=A)
RightInverse _∙_ i inv = ∀ x → x ∙ inv x ≅ i

record HasInverse {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_∙_ : BinOp A) (i : A) (_⁻¹ : A → A) : Set (ℓA ⊔ ℓ=A) where
    field
        overlap {{has-identity}} : HasIdentity _∙_ i
        overlap {{inverse-is-congruent}} : IsCongruent _⁻¹
        left-inverse : LeftInverse _∙_ i _⁻¹
        right-inverse : RightInverse _∙_ i _⁻¹

open HasInverse {{...}}

private
    commute-inverse : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → {_∙_ : BinOp A} {i : A} {_⁻¹ : A → A} → {{C : IsCommutative _∙_}} → {{HI : HasIdentity _∙_ i}} → 
        LeftInverse _∙_ i _⁻¹ → RightInverse _∙_ i _⁻¹
    commute-inverse {_} {_} {{_}} {_∙_} {i} {inv} left-inv x = begin≅
        x ∙ inv x   ≅< commute-on _∙_ x (inv x) >
        inv x ∙ x   ≅< left-inv x >
        i           ∎

has-inverse-commute : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → {_∙_ : BinOp A} {i : A} {_⁻¹ : A → A} → {{C : IsCommutative _∙_}} → {{HI : HasIdentity _∙_ i}} → {{IC : IsCongruent _⁻¹}} →
        LeftInverse _∙_ i _⁻¹ → HasInverse _∙_ i _⁻¹
has-inverse-commute left-inv = record { left-inverse = left-inv; right-inverse = commute-inverse left-inv }

left-inverse-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (id : A) → (inv : A → A) → {{HasInverse _∙_ id inv}} → (a : A) → inv a ∙ a ≅ id
left-inverse-on _ _ _ = left-inverse

right-inverse-on : {A : Set ℓA} → {{SA : Setoid ℓ=A A}} → (_∙_ : BinOp A) → (id : A) → (inv : A → A) → {{HasInverse _∙_ id inv}} → (a : A) → a ∙ inv a ≅ id
right-inverse-on _ _ _ = right-inverse

record BiInjective {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
    {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} {{SC : Setoid ℓ=C C}}
    (_∙_ : A → B → C) : Set (ℓA ⊔ ℓB ⊔ ℓC ⊔ ℓ=A ⊔ ℓ=B ⊔ ℓ=C) where
    field
        left-injective : (a : A) → Injective (a ∙_)
        right-injective : (b : B) → Injective (_∙ b)

open BiInjective {{...}}

left-injective-on : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
     {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {{SC : Setoid ℓ=C C}} →
     (_∙_ : A → B → C) → {{BI : BiInjective _∙_}} → (a : A) → Injective (a ∙_)
left-injective-on _ = left-injective

right-injective-on : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
     {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {{SC : Setoid ℓ=C C}} →
     (_∙_ : A → B → C) → {{BI : BiInjective _∙_}} → (b : B) → Injective (_∙ b)
right-injective-on _ = right-injective