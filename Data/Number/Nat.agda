module Data.Number.Nat where

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
open import Structure.Algebraic.Ringoid
open import Relation
open import Relation.Properties
open import Relation.Order.Partial
open import Relation.Order.Total
open import Relation.Equivalence.Structural.Properties Ordering
open import Data.Either
open import Relation.Equivalence.Structural
open import Function.Unary.Properties
open import Logic
open import Data.Number.Nat.Base

private
    +-commute-lemma : (x y : ℕ) → (suc x + y) ≅ (x + suc y)
    +-commute-lemma 0ℕ y = begin≅
        1ℕ + y              ≅<>
        suc y               ≅< symmetric-on ℕ (left-identity-on _+_ (suc y)) >
        0ℕ + suc y          ∎
    +-commute-lemma (suc x) y = begin≅
        suc (suc x) + y     ≅<>
        suc (suc x + y)     ≅< congruent-on suc (+-commute-lemma x y) >
        suc (x + suc y)     ≅<>
        suc x + suc y       ∎

    +-commute : Commute _+_
    +-commute 0ℕ ys = begin≅
        0ℕ + ys            ≅<>
        ys                  ≅< symmetric-on ℕ (right-identity-on _++_ ys) >
        ys + 0ℕ            ∎
    +-commute (suc x) y = begin≅
        suc x + y           ≅<>
        suc (x + y)         ≅< congruent-on suc (+-commute x y) >
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

    +-commutative-monoid : CommutativeMonoid _+_ 0ℕ
    +-commutative-monoid = record {}

    +-bi-injective : BiInjective _+_
    +-bi-injective = record {left-injective = +-left-injective; right-injective = +-right-injective}

_*_ : BinOp ℕ
0ℕ * n = 0ℕ
suc m * n = n + (m * n)

infixr 10 _*_

private
    *-left-congruent : LeftCongruent _*_
    *-left-congruent {0ℕ}  _ = 0ℕ=
    *-left-congruent {suc a} {b} {c} b=c = bi-congruent _+_ b=c (*-left-congruent {a} {b} {c} b=c)

    *-left-zero : LeftZero _*_ 0ℕ
    *-left-zero _ = 0ℕ=

    *-right-zero : RightZero _*_ 0ℕ
    *-right-zero 0ℕ = 0ℕ=
    *-right-zero (suc n) = *-right-zero n

    *-distributes-over-+ : (a b c : ℕ) → a * (b + c) ≅ a * b + a * c
    *-distributes-over-+ 0ℕ _ _ = 0ℕ=
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
    *-left-id 0ℕ = 0ℕ=
    *-left-id (suc n) = right-identity-on _+_ (suc n)

    *-right-id : RightIdentity _*_ 1ℕ
    *-right-id 0ℕ = 0ℕ=
    *-right-id (suc n) = left-congruent-on _+_ (*-right-id n)
    
    *-commute : Commute _*_
    *-commute 0ℕ n = symmetric-on ℕ (*-right-zero n)
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
    *-assoc 0ℕ _ _ = 0ℕ=
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

    *-ringoid : Ringoid _*_ _+_
    *-ringoid = record { left-distribute = *-distributes-over-+ ; right-distribute = *-right-distributes }

    *-has-zero : HasZero _*_ 0ℕ
    *-has-zero = record {left-zero = *-left-zero; right-zero = *-right-zero}

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
    ≤-antisymmetric z≤ z≤ = 0ℕ=
    ≤-antisymmetric (s≤s x≤y) (s≤s y≤x) = congruent-on suc (≤-antisymmetric x≤y y≤x)

    ≤-left-congruent : {a1 a2 b : ℕ} → a1 ≅ a2 → a1 ≤ b → a2 ≤ b
    ≤-left-congruent 0ℕ= z≤ = z≤
    ≤-left-congruent (suc= a1=a2) (s≤s a1≤b) = s≤s (≤-left-congruent a1=a2 a1≤b)

    ≤-right-congruent : {a b1 b2 : ℕ} → b1 ≅ b2 → a ≤ b1 → a ≤ b2
    ≤-right-congruent 0ℕ= a≤b1 = a≤b1
    ≤-right-congruent (suc= _) z≤ = z≤
    ≤-right-congruent (suc= b1=b2) (s≤s a≤b1) = s≤s (≤-right-congruent b1=b2 a≤b1)

    ≤-compare : (m n : ℕ) → Either (m ≤ n) (n ≤ m)
    ≤-compare 0ℕ _ = left z≤
    ≤-compare _ 0ℕ = right z≤
    ≤-compare (suc m) (suc n) with ≤-compare m n
    ... | left m≤n      = left (s≤s m≤n)
    ... | right n≤m     = right (s≤s n≤m)

    suc-le-injective : { m n : ℕ } → suc m ≤ suc n → m ≤ n
    suc-le-injective (s≤s m≤n) = m≤n

    ≤-trichotomy : (m n : ℕ) → Tri _≅_ _≤_ m n
    ≤-trichotomy 0ℕ 0ℕ = triE 0ℕ=
    ≤-trichotomy 0ℕ (suc n) = triL z≤ (λ ()) (λ ())
    ≤-trichotomy (suc m) 0ℕ = triG (λ ()) (λ ()) z≤
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

cancel-left-+-≤ : (a b c : ℕ) → (a + b) ≤ (a + c) → b ≤ c
cancel-left-+-≤ 0ℕ b c ab≤ac = ab≤ac
cancel-left-+-≤ (suc a) b c (s≤s ab≤ac) = cancel-left-+-≤ a b c ab≤ac 

nat-not-nonzero-plus-itself : (m n : ℕ) → ¬ (suc m + n ≅ n)
nat-not-nonzero-plus-itself m 0ℕ ()
nat-not-nonzero-plus-itself m (suc n) (suc= eq) = nat-not-nonzero-plus-itself m n (begin≅
    suc m + n   ≅< +-commute-lemma m n >
    m + suc n   ≅< eq >
    n           ∎)

nat-not-itself-plus-nonzero : (m n : ℕ) → ¬ (n + suc m ≅ n)
nat-not-itself-plus-nonzero m n eq = nat-not-nonzero-plus-itself m n (begin≅
    suc m + n       ≅< commute-on _+_ (suc m) n >
    n + suc m       ≅< eq >
    n               ∎)

cancel-right-multiplication-nonzero : {x y z : ℕ} → (y * suc x ≅ z * suc x) → y ≅ z
cancel-right-multiplication-nonzero {x} {suc y} {suc z} sysx=szsx = suc= (cancel-right-multiplication-nonzero (left-injective-on _+_ (suc x) sysx=szsx))
cancel-right-multiplication-nonzero {suc x} {0ℕ} {suc z} ()
cancel-right-multiplication-nonzero {suc x} {suc y} {0ℕ} ()
cancel-right-multiplication-nonzero {_} {0ℕ} {0ℕ} _ = 0ℕ=

cancel-left-multiplication-nonzero : {x y z : ℕ} → (suc x * y ≅ suc x * z) → y ≅ z
cancel-left-multiplication-nonzero {x} {y} {z} eq = cancel-right-multiplication-nonzero {x} {y} {z} (begin≅
    y * suc x   ≅< commute-on _*_ y (suc x) >
    suc x * y   ≅< eq >
    suc x * z   ≅< commute-on _*_ (suc x) z >
    z * suc x   ∎)

product-is-zero : {a b : ℕ} → (a * b ≅ 0ℕ) → Either (a ≅ 0ℕ) (b ≅ 0ℕ)
product-is-zero {0ℕ} {_} _ = left 0ℕ=
product-is-zero {_} {0ℕ} _ = right 0ℕ=
-- compiler can prove no other cases

ordering-to-subtraction : {a b : ℕ} → a ≤ b → Σ ℕ (λ c → a + c ≅ b)
ordering-to-subtraction {0ℕ} {b} z≤ = b , reflexive-on ℕ b
ordering-to-subtraction {suc a} {suc b} (s≤s a≤b) with ordering-to-subtraction a≤b
... | c , eq    = c , suc= eq

subtraction-to-ordering : {a b c : ℕ} → a + c ≅ b → a ≤ b
subtraction-to-ordering {suc a} {suc b} {c} (suc= ac=b) = s≤s (subtraction-to-ordering ac=b)
subtraction-to-ordering {0ℕ} _ = z≤

multiplication-preserves-≤ : {a b c d : ℕ} → a ≤ b → c ≤ d → a * c ≤ b * d
multiplication-preserves-≤ {a} {b} {c} {d} a≤b c≤d with ordering-to-subtraction a≤b | ordering-to-subtraction c≤d
... | x , a+x=b | y , c+y=d = subtraction-to-ordering (symmetric-on ℕ (begin≅
        b * d                               ≅< bi-congruent _*_ (symmetric-on ℕ a+x=b) (symmetric-on ℕ c+y=d) >
        (a + x) * (c + y)                   ≅< left-distribute-on _*_ _+_ (a + x) c y >
        (a + x) * c + (a + x) * y           ≅< bi-congruent _+_ (right-distribute-on _*_ _+_ a x c) (right-distribute-on _*_ _+_ a x y) >
        (a * c + x * c) + (a * y + x * y)   ≅< right-associate-on _+_ (a * c) (x * c) (a * y + x * y) >
        a * c + (x * c + (a * y + x * y))   ∎))

cancel-right-multiplication-nonzero-≤ : {x y z : ℕ} → x * suc z ≤ y * suc z → x ≤ y
cancel-right-multiplication-nonzero-≤ {x} {y} {0ℕ} x1≤y1 = bi-congruent-order _≤_ (symmetric-on ℕ (right-identity-on _*_ x)) (symmetric-on ℕ (right-identity-on _*_ y)) x1≤y1
cancel-right-multiplication-nonzero-≤ {0ℕ} _ = z≤
cancel-right-multiplication-nonzero-≤ {x} {0ℕ} xsz≤ysz = reflexive-equiv-order-on _≤_ (cancel-right-multiplication-nonzero-≤-lemma xsz≤ysz)
    where   cancel-right-multiplication-nonzero-≤-lemma : {x y : ℕ} → x * suc y ≤ 0ℕ → x ≅ 0ℕ
            cancel-right-multiplication-nonzero-≤-lemma {0ℕ} _ = 0ℕ=
cancel-right-multiplication-nonzero-≤ {suc x} {suc y} {z} xsz≤ysz = 
    s≤s (cancel-right-multiplication-nonzero-≤ (cancel-left-+-≤ (suc z) (x * suc z) (y * suc z) xsz≤ysz))

cancel-left-multiplication-nonzero-≤ : {x y z : ℕ} → suc x * y ≤ suc x * z → y ≤ z
cancel-left-multiplication-nonzero-≤ {x} {y} {z} sxy≤sxz = cancel-right-multiplication-nonzero-≤ (bi-congruent-order _≤_ (commute-on _*_ y (suc x)) (commute-on _*_ z (suc x)) sxy≤sxz)

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
    c ++ suc a      ≅< symmetric-on ℕ (+-commute-lemma c a) >
    suc c ++ a      ≅< eq >
    b               ∎))
... | tri> c eq = tri> c (suc= (begin≅
    c ++ suc b      ≅< symmetric-on ℕ (+-commute-lemma c b) >
    suc c ++ b      ≅< eq >
    a               ∎))  