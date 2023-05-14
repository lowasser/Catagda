module Definitions.Function.Isomorphism where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Function.Composition
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties

open Setoid{{...}}
open IsCongruent{{...}}

private
    variable
        ℓA ℓB ℓ=A ℓ=B : Level

record Iso {A : Set ℓA} {B : Set ℓB} {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} (f : A → B) (g : B → A) : Set (ℓA ⊔ ℓB ⊔ ℓ=A ⊔ ℓ=B) where
    field
        compose-is-identity : ∀ a → g (f a) ≅ a
        reverse-compose-is-identity : ∀ b → f (g b) ≅ b
        is-congruent : IsCongruent f
        inverse-is-congruent : IsCongruent g

open Iso {{...}}

_⁻¹ : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → { f : A → B } {g : B → A} → Iso f g → Iso g f
iso ⁻¹ = record {
        reverse-compose-is-identity = Iso.compose-is-identity iso;
        compose-is-identity = Iso.reverse-compose-is-identity iso;
        inverse-is-congruent = Iso.is-congruent iso;
        is-congruent = Iso.inverse-is-congruent iso}

private
    lift2 : {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓB} → (A → B) → (B → B → C) → A → A → C
    lift2 f _∙_ a1 a2 = f a1 ∙ f a2 

    iso-injective : {A : Set ℓA} {B : Set ℓB} {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → { f : A → B } { g : B → A } → Iso f g → Injective f
    iso-injective {_} {_} {_} {_} {A} {B} {f} {g} iso {a1} {a2} fa1≅fa2 = begin≅
        a1          ≅< symmetric-on A (Iso.compose-is-identity iso a1) >
        g (f a1)    ≅< IsCongruent.congruent (Iso.inverse-is-congruent iso) fa1≅fa2 >
        g (f a2)    ≅< Iso.compose-is-identity iso a2 >
        a2          ∎

iso-is-injective : {A : Set ℓA} {B : Set ℓB} {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → { f : A → B } { g : B → A } → Iso f g → IsInjective f
iso-is-injective iso = record { injective = iso-injective iso }

private 
    surjective-reverse-compose-is-identity : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} →
        (f : A → B) → (surjf : Surjective f) → ∀ b → f (preimage f surjf b) ≅ b
    surjective-reverse-compose-is-identity f surjf b = preimage-proof f surjf b

    injective-surjective-compose-is-identity : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} →
        (f : A → B) → (surjf : Surjective f) → (injf : Injective f) → ∀ a → preimage f surjf (f a) ≅ a
    injective-surjective-compose-is-identity f surjf injf a = injf (preimage-proof f surjf (f a)) 

    injective-surjective-preimage-is-congruent : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} →
        (f : A → B) → (surjf : Surjective f) → (injf : Injective f) → Congruent (preimage f surjf)
    injective-surjective-preimage-is-congruent {_} {_} {_} {_} {_} {B} f surjf injf {b1} {b2} b1≅b2 = injf lemma3
        where   lemma1 : f (preimage f surjf b1) ≅ b1
                lemma1 = preimage-proof f surjf b1
                lemma2 : f (preimage f surjf b2) ≅ b2
                lemma2 = preimage-proof f surjf b2
                lemma3 : f (preimage f surjf b1) ≅ f (preimage f surjf b2)
                lemma3 = begin≅
                    f (preimage f surjf b1) ≅< lemma1 >
                    b1                      ≅< b1≅b2 >
                    b2                      ≅< symmetric-on B lemma2 >
                    f (preimage f surjf b2) ∎

injective-surjective-to-iso : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} →
        (f : A → B) → (surjf : Surjective f) → (injf : Injective f) → {{ICF : IsCongruent f}} → Iso f (preimage f surjf)
injective-surjective-to-iso f surjf injf {{icf}} = record {
        compose-is-identity = injective-surjective-compose-is-identity f surjf injf;
        reverse-compose-is-identity = surjective-reverse-compose-is-identity f surjf;
        is-congruent = icf;
        inverse-is-congruent = record {congruent = injective-surjective-preimage-is-congruent f surjf injf }
    } 