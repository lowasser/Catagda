module Definitions.Function.Composition.Properties where

open import Agda.Primitive
open import Definitions.Function.Composition
open import Definitions.Function.Unary.Properties
open import Definitions.Setoid
open import Definitions.Setoid.Equation

∘-congruent : {ℓA ℓB ℓC : Level} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid A}} → {{SB : Setoid B}} → {{SC : Setoid C}} →
    (f : A → B) → {{ICf : IsCongruent f}} → (g : B → C) → {{ICg : IsCongruent g}} → Congruent (g ∘ f)
∘-congruent f g {a1} {a2} a1≈a2 = begin≈
    (g ∘ f) a1      ≈<>
    g (f a1)        ≈< congruent-on g (congruent-on f a1≈a2) >
    g (f a2)        ≈<>
    (g ∘ f) a2      ∎
