module Definitions.Function.Unary.Properties where

open import Agda.Primitive
open import Definitions.Relation
open import Definitions.Setoid
open import Definitions.DependentPair

open Setoid {{...}}

Congruent : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (A → B) → {{AS : Setoid A}} → {{BS : Setoid B}} → Set (ℓA ⊔ ℓB)
Congruent f = ∀ {a1 a2} → a1 ≈ a2 → f a1 ≈ f a2

record IsCongruent {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} (f : A → B) {{AS : Setoid A}} {{BS : Setoid B}} : Set (ℓA ⊔ ℓB) where
    field
        congruent : Congruent f

open IsCongruent{{...}}

congruent-on : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{AS : Setoid A}} → {{BS : Setoid B}} → 
    {{IsCongruent f}} → Congruent f
congruent-on _ = congruent

Injective : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (A → B) → {{AS : Setoid A}} → {{BS : Setoid B}} → Set (ℓA ⊔ ℓB)
Injective f = ∀ {a1 a2} → f a1 ≈ f a2 → a1 ≈ a2

record IsInjective {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} (f : A → B) {{AS : Setoid A}} {{BS : Setoid B}} : Set (ℓA ⊔ ℓB) where
    field
        injective : Injective f

open IsInjective {{...}}

injective-on : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{AS : Setoid A}} → {{BS : Setoid B}} → 
    {{IsInjective f}} → Injective f
injective-on _ = injective

Surjective : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (A → B) → {{BS : Setoid B}} → Set (ℓA ⊔ ℓB)
Surjective {_} {_} {A} f = ∀ b → Σ A (λ a → f a ≈ b)

preimage : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid B}} → Surjective f → B → A
preimage _ surj b = fstΣ (surj b)

preimage-proof :  {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid B}} → (surj : Surjective f) → (b : B) → (f (preimage f surj b) ≈ b)
preimage-proof _ surj b = sndΣ (surj b)

record IsSurjective {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} (f : A → B) {{BS : Setoid B}} : Set (ℓA ⊔ ℓB) where
    field
        surjective : Surjective f

open IsSurjective {{...}}

surjective-on : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid B}} → {{IsSurjective f}} → Surjective f
surjective-on _ = surjective

preimage-on : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid B}} → {{IsSurjective f}} → B → A
preimage-on f b = fstΣ (surjective-on f b)

preimage-proof-on : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {{BS : Setoid B}} → {{ISF : IsSurjective f}} → (b : B) → f (preimage-on f b) ≈ b
preimage-proof-on f b = sndΣ (surjective-on f b)