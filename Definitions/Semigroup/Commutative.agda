module Definitions.Semigroup.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid
open import Definitions.Setoid.Equation

private
    variable
        ℓS ℓ=S : Level


record CommutativeSemigroup {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{commutative-magma}} : CommutativeMagma _∙_
        overlap {{base-semigroup}} : Semigroup _∙_

    open Semigroup {{...}}
    open IsAssociative {{...}}
    open CommutativeMagma {{...}}
    open IsCommutative {{...}}
    open Setoid {{...}}
    open Magma {{...}}

open Setoid {{...}}

-- A commutative semigroup is necessary and sufficient to just rearrange elements' parentheses and order.

<ab><cd>-to-<ad><bc>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c d : S) → ((a ∙ b) ∙ (c ∙ d)) ≅ ((a ∙ d) ∙ (b ∙ c))
<ab><cd>-to-<ad><bc>-on _∙_ a b c d = begin≅
        (a ∙ b) ∙ (c ∙ d)       ≅< left-associate-on _∙_ (a ∙ b) c d >
        ((a ∙ b) ∙ c) ∙ d       ≅< commute-on _∙_ ((a ∙ b) ∙ c) d >
        d ∙ ((a ∙ b) ∙ c)       ≅< left-congruent-on _∙_ (right-associate-on _∙_ a b c) >
        d ∙ (a ∙ (b ∙ c))       ≅< left-associate-on _∙_ d a (b ∙ c) >
        (d ∙ a) ∙ (b ∙ c)       ≅< right-congruent-on _∙_ (commute-on _∙_ d a) >
        (a ∙ d) ∙ (b ∙ c)       ∎

<ab><cd>-to-<ad><cb>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c d : S) → ((a ∙ b) ∙ (c ∙ d)) ≅ ((a ∙ d) ∙ (c ∙ b))
<ab><cd>-to-<ad><cb>-on _∙_ a b c d = begin≅
        (a ∙ b) ∙ (c ∙ d)       ≅< <ab><cd>-to-<ad><bc>-on _∙_ a b c d >
        (a ∙ d) ∙ (b ∙ c)       ≅< left-congruent-on _∙_ (commute-on _∙_ b c) >
        (a ∙ d) ∙ (c ∙ b)       ∎

a<bc>-to-b<ac>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → a ∙ (b ∙ c) ≅ b ∙ (a ∙ c)
a<bc>-to-b<ac>-on _∙_ a b c = begin≅
        a ∙ (b ∙ c)             ≅< left-associate-on _∙_ a b c >
        (a ∙ b) ∙ c             ≅< right-congruent-on _∙_ (commute-on _∙_ a b) >
        (b ∙ a) ∙ c             ≅< right-associate-on _∙_ b a c >
        b ∙ (a ∙ c)             ∎

a<bc>-to-b<ca>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → a ∙ (b ∙ c) ≅ b ∙ (c ∙ a)
a<bc>-to-b<ca>-on _∙_ a b c = begin≅
        a ∙ (b ∙ c)             ≅< a<bc>-to-b<ac>-on _∙_ a b c >
        b ∙ (a ∙ c)             ≅< left-congruent-on _∙_ (commute-on _∙_ a c) >
        b ∙ (c ∙ a)             ∎

<ab><cd>-to-<ac><bd>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c d : S) → (a ∙ b) ∙ (c ∙ d) ≅ (a ∙ c) ∙ (b ∙ d)
<ab><cd>-to-<ac><bd>-on _∙_ a b c d = begin≅
    (a ∙ b) ∙ (c ∙ d)           ≅< left-associate-on _∙_ (a ∙ b) c d >
    ((a ∙ b) ∙ c) ∙ d           ≅< right-congruent-on _∙_ (right-associate-on _∙_ a b c) >
    (a ∙ (b ∙ c)) ∙ d           ≅< right-congruent-on _∙_ (left-congruent-on _∙_ (commute-on _∙_ b c)) >
    (a ∙ (c ∙ b)) ∙ d           ≅< right-congruent-on _∙_ (left-associate-on _∙_ a c b) >
    ((a ∙ c) ∙ b) ∙ d           ≅< right-associate-on _∙_ (a ∙ c) b d >
    (a ∙ c) ∙ (b ∙ d)           ∎

<ab><cd>-to-<cb><ad>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c d : S) → (a ∙ b) ∙ (c ∙ d) ≅ (c ∙ b) ∙ (a ∙ d)
<ab><cd>-to-<cb><ad>-on _∙_ a b c d = begin≅
    (a ∙ b) ∙ (c ∙ d)       ≅< <ab><cd>-to-<ad><cb>-on _∙_ a b c d >
    (a ∙ d) ∙ (c ∙ b)       ≅< commute-on _∙_ (a ∙ d) (c ∙ b) >
    (c ∙ b) ∙ (a ∙ d)       ∎

a<bc>-to-c<ba>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → a ∙ (b ∙ c) ≅ c ∙ (b ∙ a)
a<bc>-to-c<ba>-on _∙_ a b c = begin≅
    a ∙ (b ∙ c)     ≅< left-associate-on _∙_ a b c >
    (a ∙ b) ∙ c     ≅< commute-on _∙_ (a ∙ b) c >
    c ∙ (a ∙ b)     ≅< left-congruent-on _∙_ (commute-on _∙_ a b) >
    c ∙ (b ∙ a)     ∎  

<ab>c-to-a<cb>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → (a ∙ b) ∙ c ≅ a ∙ (c ∙ b)
<ab>c-to-a<cb>-on _∙_ a b c = begin≅
    (a ∙ b) ∙ c     ≅< right-associate-on _∙_ a b c >
    a ∙ (b ∙ c)     ≅< left-congruent-on _∙_ (commute-on _∙_ b c) >
    a ∙ (c ∙ b)     ∎

a<bc>-to-<ac>b-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → a ∙ (b ∙ c) ≅ (a ∙ c) ∙ b
a<bc>-to-<ac>b-on _∙_ a b c = begin≅
    a ∙ (b ∙ c)     ≅< left-congruent-on _∙_ (commute-on _∙_ b c) >
    a ∙ (c ∙ b)     ≅< left-associate-on _∙_ a c b >
    (a ∙ c) ∙ b     ∎

<ab>c-to-<ac>b-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → (a ∙ b) ∙ c ≅ (a ∙ c) ∙ b
<ab>c-to-<ac>b-on _∙_ a b c = begin≅
    (a ∙ b) ∙ c     ≅< right-associate-on _∙_ a b c >
    a ∙ (b ∙ c)     ≅< a<bc>-to-<ac>b-on _∙_ a b c >
    (a ∙ c) ∙ b     ∎

<ab>c-to-<bc>a-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → (a ∙ b) ∙ c ≅ (b ∙ c) ∙ a
<ab>c-to-<bc>a-on _∙_ a b c = begin≅
    (a ∙ b) ∙ c     ≅< right-associate-on _∙_ a b c >
    a ∙ (b ∙ c)     ≅< commute-on _∙_ a (b ∙ c) >
    (b ∙ c) ∙ a     ∎

<ab>c-to-b<ca>-on : {S : Set ℓS} {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{CS : CommutativeSemigroup _∙_}} → (a b c : S) → (a ∙ b) ∙ c ≅ b ∙ (c ∙ a)
<ab>c-to-b<ca>-on _∙_ a b c = begin≅
    (a ∙ b) ∙ c     ≅< <ab>c-to-<bc>a-on _∙_ a b c >
    (b ∙ c) ∙ a     ≅< right-associate-on _∙_ b c a >
    b ∙ (c ∙ a)     ∎