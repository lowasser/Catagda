open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Function.Properties where

open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.Setoid.Equation
open import Definitions.Function.Composition

open Setoid {{...}}

private
    variable
        ℓA ℓB ℓC ℓ=A ℓ=B ℓ=C : Level

record _Congruent→_ (A : Set ℓA) (B : Set ℓB) {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} : Set (ℓA ⊔ ℓB ⊔ ℓ=A ⊔ ℓ=B) where 
    field
        cong-func : A → B
        is-congruent : Congruent cong-func

open _Congruent→_

id-congruent : (A : Set ℓA) → {{SA : Setoid ℓ=A A}} → A Congruent→ A
id-congruent _ = record {
    cong-func = λ a → a;
    is-congruent = λ a=b → a=b}

_cong$_ : {A : Set ℓA} {B : Set ℓB} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → A Congruent→ B → A → B
congf cong$ a = cong-func congf a

_cong∘_ : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} → {{SA : Setoid ℓ=A A}} → {{SB : Setoid ℓ=B B}} → {{SC : Setoid ℓ=C C}} → B Congruent→ C → A Congruent→ B → A Congruent→ C
f cong∘ g = record {
    cong-func = cong-func f ∘ cong-func g;
    is-congruent = λ {a1} {a2} a1=a2 → is-congruent f (is-congruent g (a1=a2))}

data ≡→ (A : Set ℓA) (B : Set ℓB) {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} : Relation (A Congruent→ B) where
    fequiv : (f g : A Congruent→ B) → ((a : A) → f cong$ a ≅ g cong$ a) → ≡→ A B f g

private
    ≡→-reflexive : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Reflexive (≡→ A B)
    ≡→-reflexive A B congf = fequiv congf congf (λ a → reflexive-on B (congf cong$ a))
        where open _Congruent→_ congf

    ≡→-symmetric : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Symmetric (≡→ A B)
    ≡→-symmetric A B (fequiv fa fb eq) = fequiv fb fa (λ a → symmetric-on B (eq a))

    ≡→-transitive : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Transitive (≡→ A B)
    ≡→-transitive A B (fequiv f g feqg) (fequiv g h geqh) = fequiv f h (λ a → begin≅
        f cong$ a      ≅< feqg a >
        g cong$ a      ≅< geqh a >
        h cong$ a      ∎)

≡→-equivalence : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Equivalence (≡→ A B)
≡→-equivalence A B = make-equivalence (≡→ A B) (≡→-reflexive A B) (≡→-transitive A B) (≡→-symmetric A B)  