module Function.Unary.Properties where

open import Agda.Primitive
open import Relation
open import Structure.Setoid
open import Agda.Builtin.Sigma
open import Logic

open Setoid {{...}}

private
    variable
        ℓA ℓB ℓ=A ℓ=B : Level

Congruent : {A : Set ℓA} {B : Set ℓB} → (A → B) → {{AS : Setoid ℓ=A A}} → {{BS : Setoid ℓ=B B}} → Set (ℓA ⊔ ℓ=A ⊔ ℓ=B)
Congruent f = ∀ {a1 a2} → a1 ≅ a2 → f a1 ≅ f a2

record IsCongruent {A : Set ℓA} {B : Set ℓB} (f : A → B) {{AS : Setoid ℓ=A A}} {{BS : Setoid ℓ=B B}} : Set (ℓA ⊔ ℓ=A ⊔ ℓ=B) where
    field
        congruent : Congruent f

open IsCongruent{{...}}

congruent-on : {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{AS : Setoid ℓ=A A}} → {{BS : Setoid ℓ=B B}} → 
    {{IsCongruent f}} → Congruent f
congruent-on _ = congruent

Injective : {A : Set ℓA} {B : Set ℓB} → (A → B) → {{AS : Setoid ℓ=A A}} → {{BS : Setoid ℓ=B B}} → Set (ℓA ⊔ ℓ=A ⊔ ℓ=B)
Injective f = ∀ {a1 a2} → f a1 ≅ f a2 → a1 ≅ a2

record IsInjective {A : Set ℓA} {B : Set ℓB} (f : A → B) {{AS : Setoid ℓ=A A}} {{BS : Setoid ℓ=B B}} : Set (ℓA ⊔ ℓ=A ⊔ ℓ=B) where
    field
        injective : Injective f

open IsInjective {{...}}

injective-on : {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{AS : Setoid ℓ=A A}} → {{BS : Setoid ℓ=B B}} → 
    {{IsInjective f}} → Injective f
injective-on _ = injective

Surjective : {ℓA ℓB ℓ=B : Level} {A : Set ℓA} {B : Set ℓB} → (A → B) → {{BS : Setoid ℓ=B B}} → Set (ℓA ⊔ ℓB ⊔ ℓ=B)
Surjective {_} {_} {_} {A} f = ∀ b → ∃ A (λ a → f a ≅ b)

preimage : {ℓA ℓB ℓ=B : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid ℓ=B B}} → Surjective f → B → A
preimage _ surj b = fst (surj b)

preimage-proof : {ℓA ℓB ℓ=B : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid ℓ=B B}} → (surj : Surjective f) → (b : B) → f (preimage f surj b) ≅ b
preimage-proof _ surj b = snd (surj b)

record IsSurjective {A : Set ℓA} {B : Set ℓB} (f : A → B) {{BS : Setoid ℓ=B B}} : Set (ℓA ⊔ ℓB ⊔ ℓ=B) where
    field
        surjective : Surjective f

open IsSurjective {{...}}

surjective-on : {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid ℓ=B B}} → {{IsSurjective f}} → Surjective f
surjective-on _ = surjective

preimage-on : {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid ℓ=B B}} → {{IsSurjective f}} → B → A
preimage-on f b = fst (surjective-on f b)

preimage-proof-on : {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid ℓ=B B}} → {{ISF : IsSurjective f}} → (b : B) → f (preimage-on f b) ≅ b
preimage-proof-on f b = snd (surjective-on f b)