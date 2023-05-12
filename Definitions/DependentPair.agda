module Definitions.DependentPair where

open import Agda.Primitive

data Σ {ℓA ℓB : Level} (A : Set ℓA) (B : A → Set ℓB) : Set (ℓA ⊔ ℓB) where
    _,_ : (x : A) → B x → Σ A B

fstΣ : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB} → Σ A B → A
fstΣ (a , _) = a

sndΣ : {ℓA ℓB : Level} {A : Set ℓA} {B : A → Set ℓB} → (p : Σ A B) → B (fstΣ p)
sndΣ (_ , b) = b