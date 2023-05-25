open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Function.Properties where

open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid.Equation
open import Definitions.Function.Composition

open Setoid {{...}}

private
    variable
        ℓA ℓB ℓC ℓD ℓ=A ℓ=B ℓ=C ℓ=D : Level

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

data Pointwise= (A : Set ℓA) (B : Set ℓB) {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} : Relation (A Congruent→ B) where
    fequiv : (f g : A Congruent→ B) → ((a : A) → f cong$ a ≅ g cong$ a) → Pointwise= A B f g

private
    pointwise=-reflexive : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Reflexive (Pointwise= A B)
    pointwise=-reflexive A B congf = fequiv congf congf (λ a → reflexive-on B (congf cong$ a))
        where open _Congruent→_ congf

    pointwise=-symmetric : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Symmetric (Pointwise= A B)
    pointwise=-symmetric A B (fequiv fa fb eq) = fequiv fb fa (λ a → symmetric-on B (eq a))

    pointwise=-transitive : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Transitive (Pointwise= A B)
    pointwise=-transitive A B (fequiv f g feqg) (fequiv g h geqh) = fequiv f h (λ a → begin≅
        f cong$ a      ≅< feqg a >
        g cong$ a      ≅< geqh a >
        h cong$ a      ∎)

pointwise=-equivalence : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Equivalence (Pointwise= A B)
pointwise=-equivalence A B = make-equivalence (Pointwise= A B) (pointwise=-reflexive A B) (pointwise=-transitive A B) (pointwise=-symmetric A B)  

congruent-setoid : (A : Set ℓA) (B : Set ℓB) → {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} → Setoid (ℓA ⊔ ℓB ⊔ ℓ=A ⊔ ℓ=B) (A Congruent→ B)
congruent-setoid A B = record {_≅_ = Pointwise= A B; equivalence = pointwise=-equivalence A B}

pointwise-congruent : {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {D : Set ℓD} →
    {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} {{SC : Setoid ℓ=C C}} {{SD : Setoid ℓ=D D}} →
    (f : A Congruent→ B) (g : A Congruent→ C) (h : B → C → D) {{BCH : BiCongruent h}} →
    A Congruent→ D
pointwise-congruent f g h = record {
    cong-func = λ a → h (f cong$ a) (g cong$ a);
    is-congruent = λ {a1} {a2} a1=a2 → bi-congruent h (is-congruent f a1=a2) (is-congruent g a1=a2)}