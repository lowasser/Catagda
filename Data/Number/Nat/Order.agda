module Data.Number.Nat.Order where

open import Agda.Primitive
open import Structure.Setoid
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Relation.Equivalence.Structural.Properties ⊤
open import Data.List
open import Structure.Setoid.Equation
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Monoid.Commutative
open import Relation
open import Relation.Properties
open import Relation.Order.Partial
open import Relation.Order.Total
open import Relation.Equivalence.Structural.Properties Ordering
open import Data.Either
open import Function.Unary.Properties
open import Logic
open import Data.Number.Nat.Base
open import Data.Number.Nat.Addition

data _≤_ : Rel lzero ℕ where
    0≤ : { x : ℕ } → 0ℕ ≤ x
    s≤s : { x y : ℕ } → x ≤ y → suc x ≤ suc y

infixr 6 _≤_

private
    ≤-reflexive : Reflexive _≤_ 
    ≤-reflexive 0ℕ = 0≤
    ≤-reflexive (suc n) = s≤s (≤-reflexive n)

    ≤-transitive : Transitive _≤_
    ≤-transitive 0≤ _ = 0≤ 
    ≤-transitive (s≤s x≤y) (s≤s y≤z) = s≤s (≤-transitive x≤y y≤z)

    ≤-antisymmetric : Antisymmetric _≤_
    ≤-antisymmetric 0≤ 0≤ = 0ℕ=
    ≤-antisymmetric (s≤s x≤y) (s≤s y≤x) = congruent-on suc (≤-antisymmetric x≤y y≤x)

    ≤-reflexive-equiv : {a b : ℕ} → a ≅ b → a ≤ b
    ≤-reflexive-equiv 0ℕ= = 0≤
    ≤-reflexive-equiv (suc= a=b) = s≤s (≤-reflexive-equiv a=b)

    ≤-compare : (m n : ℕ) → Either (m ≤ n) (n ≤ m)
    ≤-compare 0ℕ _ = left 0≤
    ≤-compare _ 0ℕ = right 0≤
    ≤-compare (suc m) (suc n) with ≤-compare m n
    ... | left m≤n      = left (s≤s m≤n)
    ... | right n≤m     = right (s≤s n≤m)

    suc-le-injective : { m n : ℕ } → suc m ≤ suc n → m ≤ n
    suc-le-injective (s≤s m≤n) = m≤n

    ≤-trichotomy : (m n : ℕ) → Tri _≅_ _≤_ m n
    ≤-trichotomy 0ℕ 0ℕ = triE 0ℕ=
    ≤-trichotomy 0ℕ (suc n) = triL 0≤ (λ ()) (λ ())
    ≤-trichotomy (suc m) 0ℕ = triG (λ ()) (λ ()) 0≤
    ≤-trichotomy (suc m) (suc n) with ≤-trichotomy m n
    ... | triE m=n          = triE (suc= m=n)
    ... | triL m-le-n m≠n n-nle-m
                            = triL (s≤s m-le-n) (λ sm=sn → m≠n (injective-on suc sm=sn)) (λ sn≤sm → n-nle-m (suc-le-injective sn≤sm))
    ... | triG m-nle-n m≠n n-le-m
                            = triG (λ sm≤sn → m-nle-n (suc-le-injective sm≤sn)) (λ sm=sn → m≠n (injective-on suc sm=sn)) (s≤s n-le-m)

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
    ≤-partial-order = record { reflexive-equiv = ≤-reflexive-equiv }

    ≤-total-order : TotalOrder _≤_
    ≤-total-order = record { trichotomy = ≤-trichotomy }

private
    ≤-suc-rhs : (a b : ℕ) → a ≤ b → a ≤ suc b
    ≤-suc-rhs 0ℕ _ 0≤ = 0≤
    ≤-suc-rhs (suc a) (suc b) (s≤s a≤b) = s≤s (≤-suc-rhs a b a≤b)

addition-preserves-≤ : {a b c d : ℕ} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
addition-preserves-≤ {0ℕ} {b} {0ℕ} {d} 0≤ _ = 0≤
addition-preserves-≤ (s≤s a≤b) c≤d = s≤s (addition-preserves-≤ a≤b c≤d)
addition-preserves-≤ {0ℕ} {0ℕ} 0≤ (s≤s c≤d) = s≤s c≤d
addition-preserves-≤ {0ℕ} {suc b} {suc c} {suc d} 0≤ (s≤s c≤d) = s≤s (addition-preserves-≤ 0≤ (≤-suc-rhs c d c≤d))

cancel-left-+-≤ : (a b c : ℕ) → (a + b) ≤ (a + c) → b ≤ c
cancel-left-+-≤ 0ℕ b c ab≤ac = ab≤ac
cancel-left-+-≤ (suc a) b c (s≤s ab≤ac) = cancel-left-+-≤ a b c ab≤ac 

nat-not-nonzero-plus-itself : (m n : ℕ) → ¬ (suc m + n ≅ n)
nat-not-nonzero-plus-itself m 0ℕ ()
nat-not-nonzero-plus-itself m (suc n) (suc= eq) = nat-not-nonzero-plus-itself m n (begin≅
    suc m + n   ≅< <ab>c-to-b<ac>-on _+_ 1ℕ m n >
    m + suc n   ≅< eq >
    n           ∎)

nat-not-itself-plus-nonzero : (m n : ℕ) → ¬ (n + suc m ≅ n)
nat-not-itself-plus-nonzero m n eq = nat-not-nonzero-plus-itself m n (begin≅
    suc m + n       ≅< commute-on _+_ (suc m) n >
    n + suc m       ≅< eq >
    n               ∎)

ordering-to-subtraction : {a b : ℕ} → a ≤ b → Σ ℕ (λ c → a + c ≅ b)
ordering-to-subtraction {0ℕ} {b} 0≤ = b , reflexive-on ℕ b
ordering-to-subtraction {suc a} {suc b} (s≤s a≤b) with ordering-to-subtraction a≤b
... | c , eq    = c , suc= eq

subtraction-to-ordering : {a b c : ℕ} → a + c ≅ b → a ≤ b
subtraction-to-ordering {suc a} {suc b} {c} (suc= ac=b) = s≤s (subtraction-to-ordering ac=b)
subtraction-to-ordering {0ℕ} _ = 0≤

data TriΔ (a b : ℕ) : Set where
    tri< : (c : ℕ) → (suc c + a ≅ b) → TriΔ a b
    tri= : (a ≅ b) → TriΔ a b
    tri> : (c : ℕ) → (suc c + b ≅ a) → TriΔ a b

triΔ : (a b : ℕ) → TriΔ a b
triΔ 0ℕ 0ℕ = tri= (reflexive-on ℕ 0ℕ)
triΔ 0ℕ (suc b) = tri< b (right-identity-on _+_ (suc b))
triΔ (suc a) 0ℕ = tri> a (right-identity-on _+_ (suc a))
triΔ (suc a) (suc b) with triΔ a b
... | tri= eq   = tri= (suc= eq)
... | tri< c eq = tri< c (suc= (begin≅
    c ++ suc a      ≅< a<bc>-to-<ba>c-on _++_ c 1ℕ a >
    suc c ++ a      ≅< eq >
    b               ∎))
... | tri> c eq = tri> c (suc= (begin≅
    c ++ suc b      ≅< a<bc>-to-<ba>c-on _++_ c 1ℕ b >
    suc c ++ b      ≅< eq >
    a               ∎))  

max : BinOp ℕ
max 0ℕ n = n
max m 0ℕ = m
max (suc m) (suc n) = suc (max m n)

private
    max-commute-lemma : (a : ℕ) → max a 0ℕ ≅ a
    max-commute-lemma 0ℕ = 0ℕ=
    max-commute-lemma (suc a) = suc= (reflexive-on ℕ a)

    max-left-congruent : LeftCongruent max
    max-left-congruent {a} 0ℕ= = reflexive-on ℕ (max a 0ℕ)
    max-left-congruent {suc a} {suc b} (suc= a=b) = suc= (max-left-congruent {a} {b} a=b)
    max-left-congruent {0ℕ} (suc= b=c) = suc= b=c

    max-commute : Commute max
    max-commute 0ℕ b = symmetric-on ℕ (max-commute-lemma b)
    max-commute (suc a) 0ℕ = symmetric-on ℕ (max-commute-lemma (suc a))
    max-commute (suc a) (suc b) = suc= (max-commute a b)

instance
    max-is-commutative : IsCommutative max
    max-is-commutative = record {commute = max-commute}

    max-bi-congruent : BiCongruent max
    max-bi-congruent = bi-congruent-commutative max λ {a} → max-left-congruent {a}

    max-magma : Magma max
    max-magma = record {}

    max-commutative-magma : CommutativeMagma max
    max-commutative-magma = record {}

private
    max-left-identity : LeftIdentity max 0ℕ
    max-left-identity a = reflexive-on ℕ a

instance
    max-has-identity : HasIdentity max 0ℕ
    max-has-identity = has-identity-commute max-left-identity

private
    max-assoc : Associate max
    max-assoc 0ℕ b c = reflexive-on ℕ (max b c)
    max-assoc (suc a) 0ℕ 0ℕ = reflexive-on ℕ (suc a)
    max-assoc (suc a) 0ℕ (suc c) = begin≅
        max (suc a) (max 0ℕ (suc c))        ≅<>
        max (suc a) (suc c)                 ≅< right-congruent-on max {suc c} (symmetric-on ℕ (right-identity-on max (suc a))) >
        max (max (suc a) 0ℕ) (suc c)        ∎
    max-assoc (suc a) (suc b) 0ℕ = begin≅
        max (suc a) (max (suc b) 0ℕ)        ≅< left-congruent-on max {suc a} (right-identity-on max (suc b)) >
        max (suc a) (suc b)                 ≅< symmetric-on ℕ (right-identity-on max (suc (max a b))) >
        max (max (suc a) (suc b)) 0ℕ        ∎
    max-assoc (suc a) (suc b) (suc c) = suc= (max-assoc a b c)

instance
    max-is-associative : IsAssociative max
    max-is-associative = record {associate = max-assoc}

    max-semigroup : Semigroup max
    max-semigroup = record {}

    max-commutative-semigroup : CommutativeSemigroup max
    max-commutative-semigroup = record {}

    max-monoid : Monoid max 0ℕ
    max-monoid = record {}

    max-commutative-monoid : CommutativeMonoid max 0ℕ
    max-commutative-monoid = record {}

max-≤ : (a b : ℕ) → a ≤ b → max a b ≅ b
max-≤ 0ℕ b _ = reflexive-on ℕ b
max-≤ (suc m) (suc n) (s≤s m≤n) = suc= (max-≤ m n m≤n)

min : BinOp ℕ
min 0ℕ _ = 0ℕ
min _ 0ℕ = 0ℕ
min (suc a) (suc b) = suc (min a b)

private
    min-left-congruent : LeftCongruent min
    min-left-congruent {0ℕ} _ = 0ℕ=
    min-left-congruent {suc a} 0ℕ= = 0ℕ=
    min-left-congruent {suc a} (suc= b=c) = suc= (min-left-congruent b=c)

    min-commute : Commute min
    min-commute 0ℕ 0ℕ = 0ℕ=
    min-commute 0ℕ (suc _) = 0ℕ=
    min-commute (suc _) 0ℕ = 0ℕ=
    min-commute (suc m) (suc n) = suc= (min-commute m n)

    min-assoc : Associate min
    min-assoc 0ℕ _ _ = 0ℕ=
    min-assoc (suc _) 0ℕ _ = 0ℕ=
    min-assoc (suc _) (suc _) 0ℕ = 0ℕ=
    min-assoc (suc a) (suc b) (suc c) = suc= (min-assoc a b c)

    min-left-zero : LeftZero min 0ℕ
    min-left-zero 0ℕ = 0ℕ=
    min-left-zero (suc _) = 0ℕ=

instance
    min-is-commutative : IsCommutative min
    min-is-commutative = record {commute = min-commute}

    min-bi-congruent : BiCongruent min
    min-bi-congruent = bi-congruent-commutative min min-left-congruent

    min-is-associative : IsAssociative min
    min-is-associative = record {associate = min-assoc}

    min-magma : Magma min
    min-magma = record {}

    min-commutative-magma : CommutativeMagma min
    min-commutative-magma = record {}

    min-semigroup : Semigroup min
    min-semigroup = record {}

    min-commutative-semigroup : CommutativeSemigroup min
    min-commutative-semigroup = record {}

    min-has-zero : HasZero min 0ℕ
    min-has-zero = has-zero-commute min-left-zero

≤-min : (a b : ℕ) → a ≤ b → min a b ≅ a
≤-min 0ℕ _ _ = 0ℕ=
≤-min (suc a) (suc b) (s≤s a≤b) = suc= (≤-min a b a≤b)