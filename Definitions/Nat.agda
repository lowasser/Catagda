module Definitions.Nat where

open import Agda.Primitive
open import Definitions.Setoid
open import Agda.Builtin.Unit
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.List
open import Definitions.Setoid.Equation
open import Definitions.List.Setoid {lzero} {lzero} ⊤
open import Definitions.Monoid.Free {lzero} {lzero} ⊤
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Monoid
open import Definitions.List.Properties {lzero} {lzero} ⊤
open import Definitions.List.Concatenation.Properties {lzero} {lzero} ⊤
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid.Commutative
open import Definitions.Ringoid
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Order.Partial
open import Definitions.Relation.Order.Total
open import Definitions.Relation.Equivalence.Structural.Properties Ordering
open import Definitions.Either
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Function.Unary.Properties

open Monoid {{...}}

ℕ : Set
ℕ = FreeMonoid ⊤

_+_ : BinOp ℕ
a + b = a ∙ b

infixr 9 _+_

pattern zero = []
pattern 0ℕ = zero
pattern suc n = (tt :: n)
pattern 1ℕ = suc 0ℕ
pattern suc= x=y = (cons=[]=cons refl x=y)

open Setoid {{...}}

private
    suc-injective : Injective suc
    suc-injective {x} {y} (cons=[]=cons _ x=y) = x=y

    +-commute-lemma : (x y : ℕ) → (suc x + y) ≅ (x + suc y)
    +-commute-lemma zero y = begin≅
        suc zero + y        ≅<>
        1ℕ + y              ≅<>
        suc y               ≅< symmetric-on ℕ (left-identity-on _+_ (suc y)) >
        zero + suc y        ∎
    +-commute-lemma (suc x) y = begin≅
        suc (suc x) + y     ≅<>
        suc (suc x + y)     ≅< left-congruent-on _::_ (+-commute-lemma x y) >
        suc (x + suc y)     ≅<>
        suc x + suc y       ∎

    +-commute : Commute _+_
    +-commute [] ys = begin≅
        [] ++ ys            ≅<>
        ys                  ≅< symmetric-on ℕ (right-identity-on _++_ ys) >
        ys ++ []            ∎
    +-commute (suc x) y = begin≅
        suc x + y           ≅<>
        suc (x + y)         ≅< left-congruent-on _::_ (+-commute x y) >
        suc (y + x)         ≅<>
        suc y + x           ≅< +-commute-lemma y x >
        y + suc x           ∎

    +-left-injective : (a : ℕ) → Injective (a +_)
    +-left-injective 0ℕ ab=ac = ab=ac
    +-left-injective (suc a) (suc= ab=ac) = +-left-injective a ab=ac

    +-right-injective : (a : ℕ) → Injective (_+ a)
    +-right-injective a {b} {c} ba=ca = +-left-injective a (begin≅
        a + b       ≅< +-commute a b >
        b + a       ≅< ba=ca >
        c + a       ≅< +-commute c a >
        a + c       ∎)

instance
    +-commutative : IsCommutative  _+_
    +-commutative = record {commute = +-commute}

    +-commutative-magma : CommutativeMagma _+_
    +-commutative-magma = record {}

    +-commutative-semigroup : CommutativeSemigroup _+_
    +-commutative-semigroup = record {}

    +-commutative-monoid : CommutativeMonoid _+_ zero
    +-commutative-monoid = record {}

    +-bi-injective : BiInjective _+_
    +-bi-injective = record {left-injective = +-left-injective; right-injective = +-right-injective}

_*_ : BinOp ℕ
zero * n = zero
suc m * n = n + (m * n)

infixr 10 _*_

private
    *-left-congruent : LeftCongruent _*_
    *-left-congruent {zero} {_} {_} _ = reflexive-on ℕ zero
    *-left-congruent {suc a} {b} {c} b=c = bi-congruent _+_ b=c (*-left-congruent {a} {b} {c} b=c)

    *-left-zero : LeftZero _*_ zero
    *-left-zero x = reflexive-on ℕ zero

    *-right-zero : RightZero _*_ zero
    *-right-zero zero = reflexive-on ℕ zero
    *-right-zero (suc n) = begin≅
        suc n * zero        ≅<>
        zero + (n * zero)   ≅<>
        n * zero            ≅< *-right-zero n >
        zero                ∎

    *-distributes-over-+ : (a b c : ℕ) → a * (b + c) ≅ a * b + a * c
    *-distributes-over-+ zero _ _ = reflexive-on ℕ zero
    *-distributes-over-+ (suc a) b c = begin≅
        suc a * (b + c)             ≅<>
        (b + c) + a * (b + c)       ≅< left-congruent-on _+_ (*-distributes-over-+ a b c) >
        (b + c) + (a * b + a * c)   ≅< right-congruent-on _+_ (+-commute b c) >
        (c + b) + (a * b + a * c)   ≅< left-associate-on _+_ (c + b) (a * b) (a * c) >
        ((c + b) + a * b) + a * c   ≅< right-congruent-on _+_ (right-associate-on _+_ c b (a * b)) >
        (c + (b + a * b)) + a * c   ≅<>
        (c + suc a * b) + a * c     ≅< right-congruent-on _+_ (+-commute c (suc a * b)) >
        (suc a * b + c) + a * c     ≅< right-associate-on _+_ (suc a * b) c (a * c) >
        suc a * b + (c + a * c)     ≅<>
        suc a * b + suc a * c       ∎

    *-left-id : LeftIdentity _*_ 1ℕ
    *-left-id zero = reflexive-on ℕ zero
    *-left-id (suc n) = begin≅
        1ℕ * suc n              ≅<>
        suc n + (0ℕ * suc n)    ≅<>
        suc n + 0ℕ              ≅< right-identity-on _+_ (suc n) >
        suc n                   ∎

    *-right-id : RightIdentity _*_ 1ℕ
    *-right-id zero = reflexive-on ℕ zero
    *-right-id (suc n) = begin≅
        suc n * 1ℕ              ≅<>
        1ℕ + (n * 1ℕ)           ≅< left-congruent-on _+_ (*-right-id n) >
        1ℕ + n                  ≅<>
        suc n                   ∎
    
    *-commute : Commute _*_
    *-commute zero n = begin≅
        zero * n            ≅<>
        zero                ≅< symmetric-on ℕ (*-right-zero n) >
        n * zero            ∎
    *-commute (suc m) n = begin≅
        suc m * n           ≅<>
        n + (m * n)         ≅< left-congruent-on _+_ (*-commute m n) >
        n + (n * m)         ≅< right-congruent-on _+_ (symmetric-on ℕ (*-right-id n)) >
        (n * 1ℕ) + (n * m)  ≅< symmetric-on ℕ (*-distributes-over-+ n 1ℕ m) >
        n * (1ℕ + m)        ≅<>
        n * suc m           ∎

    *-right-distributes : (a b c : ℕ) → (a + b) * c ≅ a * c + b * c
    *-right-distributes a b c = begin≅
        (a + b) * c         ≅< *-commute (a + b) c >
        c * (a + b)         ≅< *-distributes-over-+ c a b >
        c * a + c * b       ≅< bi-congruent _+_ (*-commute c a) (*-commute c b) >
        a * c + b * c       ∎

    *-assoc : Associate _*_
    *-assoc zero b c = begin≅
        zero * (b * c)      ≅<>
        zero                ≅<>
        zero * c            ≅<>
        (zero * b) * c      ∎
    *-assoc (suc a) b c = begin≅
        suc a * (b * c)                     ≅<>
        b * c + a * (b * c)                 ≅< left-congruent-on _+_ (*-assoc a b c) >
        b * c + (a * b) * c                 ≅< symmetric-on ℕ (*-right-distributes b (a * b) c) >
        (b + a * b) * c                     ≅<>
        (suc a * b) * c                     ∎

        
instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record { commute = *-commute }

    *-bicong : BiCongruent _*_
    *-bicong = bi-congruent-commutative _*_ (λ {a b c} b=c → *-left-congruent {a} {b} {c} b=c)

    *-magma : Magma _*_
    *-magma = record {}

    *-commutative-magma : CommutativeMagma _*_
    *-commutative-magma = record {}

    *-is-associative : IsAssociative _*_
    *-is-associative = record { associate = *-assoc }

    *-semigroup : Semigroup _*_
    *-semigroup = record {}

    *-commutative-semigroup : CommutativeSemigroup _*_
    *-commutative-semigroup = record {}

    *-has-identity : HasIdentity _*_ 1ℕ
    *-has-identity = record { left-identity = *-left-id ; right-identity = *-right-id }

    *-monoid : Monoid _*_ 1ℕ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℕ
    *-commutative-monoid = record {}

    *-ringoid : Ringoid _+_ _*_
    *-ringoid = record { left-distribute = *-distributes-over-+ ; right-distribute = *-right-distributes }

data _≤_ : Rel lzero ℕ where
    z≤ : { x : ℕ } → 0ℕ ≤ x
    s≤s : { x y : ℕ } → x ≤ y → suc x ≤ suc y

infixr 6 _≤_

private
    ≤-reflexive : Reflexive _≤_ 
    ≤-reflexive 0ℕ = z≤
    ≤-reflexive (suc n) = s≤s (≤-reflexive n)

    ≤-transitive : Transitive _≤_
    ≤-transitive z≤ _ = z≤ 
    ≤-transitive (s≤s x≤y) (s≤s y≤z) = s≤s (≤-transitive x≤y y≤z)

    ≤-antisymmetric : Antisymmetric _≤_
    ≤-antisymmetric z≤ z≤ = reflexive-on ℕ 0ℕ 
    ≤-antisymmetric (s≤s x≤y) (s≤s y≤x) = bi-congruent _::_ (reflexive-on ⊤ tt) (≤-antisymmetric x≤y y≤x)

    ≤-left-congruent : {a1 a2 b : ℕ} → a1 ≅ a2 → a1 ≤ b → a2 ≤ b
    ≤-left-congruent nil=[]=nil z≤ = z≤
    ≤-left-congruent (cons=[]=cons _ a1=a2) (s≤s a1≤b) = s≤s (≤-left-congruent a1=a2 a1≤b)

    ≤-right-congruent : {a b1 b2 : ℕ} → b1 ≅ b2 → a ≤ b1 → a ≤ b2
    ≤-right-congruent nil=[]=nil a≤b1 = a≤b1
    ≤-right-congruent (cons=[]=cons _ b1=b2) z≤ = z≤
    ≤-right-congruent (cons=[]=cons x b1=b2) (s≤s a≤b1) = s≤s (≤-right-congruent b1=b2 a≤b1)

    ≤-compare : (m n : ℕ) → Either (m ≤ n) (n ≤ m)
    ≤-compare zero _ = left z≤
    ≤-compare _ zero = right z≤
    ≤-compare (suc m) (suc n) with ≤-compare m n
    ... | left m≤n      = left (s≤s m≤n)
    ... | right n≤m     = right (s≤s n≤m)

    suc-le-injective : { m n : ℕ } → suc m ≤ suc n → m ≤ n
    suc-le-injective (s≤s m≤n) = m≤n

    ≤-trichotomy : (m n : ℕ) → Tri _≅_ _≤_ m n
    ≤-trichotomy zero zero = triE (reflexive-on ℕ zero)
    ≤-trichotomy (suc m) (suc n) with ≤-trichotomy m n
    ... | triE m=n          = triE (cons=[]=cons refl m=n)
    ... | triL m-le-n m≠n n-nle-m
                            = triL (s≤s m-le-n) (λ sm=sn → m≠n (suc-injective sm=sn)) (λ sn≤sm → n-nle-m (suc-le-injective sn≤sm))
    ... | triG m-nle-n m≠n n-le-m
                            = triG (λ sm≤sn → m-nle-n (suc-le-injective sm≤sn)) (λ sm=sn → m≠n (suc-injective sm=sn)) (s≤s n-le-m)
    ≤-trichotomy zero (suc n) = triL z≤ (λ ()) (λ ())
    ≤-trichotomy (suc m) zero = triG (λ ()) (λ ()) z≤

instance
    ≤-is-reflexive : IsReflexive _≤_
    ≤-is-reflexive = record {reflexive = ≤-reflexive}

    ≤-is-transitive : IsTransitive _≤_
    ≤-is-transitive = record {transitive = ≤-transitive}
    
    ≤-is-antisymmetric : IsAntisymmetric _≤_
    ≤-is-antisymmetric = record {antisymmetric = ≤-antisymmetric}

    ≤-pre-order : PreOrder _≤_
    ≤-pre-order = record {}

    ≤-partial-order : PartialOrder _≤_
    ≤-partial-order = record { left-congruent-law = ≤-left-congruent ; right-congruent-law = ≤-right-congruent }

    ≤-total-order : TotalOrder _≤_
    ≤-total-order = record { trichotomy = ≤-trichotomy }

private
    ≤-suc-rhs : (a b : ℕ) → a ≤ b → a ≤ suc b
    ≤-suc-rhs 0ℕ _ z≤ = z≤
    ≤-suc-rhs (suc a) (suc b) (s≤s a≤b) = s≤s (≤-suc-rhs a b a≤b)

addition-preserves-≤ : {a b c d : ℕ} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
addition-preserves-≤ {0ℕ} {b} {0ℕ} {d} z≤ _ = z≤
addition-preserves-≤ (s≤s a≤b) c≤d = s≤s (addition-preserves-≤ a≤b c≤d)
addition-preserves-≤ {0ℕ} {0ℕ} z≤ (s≤s c≤d) = s≤s c≤d
addition-preserves-≤ {0ℕ} {suc b} {suc c} {suc d} z≤ (s≤s c≤d) = s≤s (addition-preserves-≤ z≤ (≤-suc-rhs c d c≤d))

subtract-both-≤ : (a b c : ℕ) → (a + b) ≤ (a + c) → b ≤ c
subtract-both-≤ 0ℕ b c ab≤ac = ab≤ac
subtract-both-≤ (suc a) b c (s≤s ab≤ac) = subtract-both-≤ a b c ab≤ac