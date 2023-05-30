module Data.Number.Int.Multiplication where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Nat.Base renaming (_+_ to _++_; _≅_ to _=N_)
open import Data.Number.Nat
    hiding (*-magma; *-is-commutative; *-commutative-magma; *-is-associative; *-semigroup; *-commutative-semigroup; *-has-identity; *-monoid; *-commutative-monoid; *-ringoid; product-is-zero)
    renaming (_*_ to _*N_; _≤_ to _≤N_)
open import Data.Number.Int.Base
open import Data.Number.Int.Addition
open import Data.Number.Int.Order
open import Function.Binary
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Ringoid
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Ring
open import Structure.Algebraic.Ring.Semi
open import Structure.Algebraic.Ring.Commutative
open import Data.Either
open import Structure.Algebraic.IntegralDomain
open import Relation.Order.Partial
open import Logic

_*_ : BinOp ℤ
int px nx * int py ny = int (px *N py ++ nx *N ny) (px *N ny ++ nx *N py)

infixr 10 _*_

private
    *-left-congruent : LeftCongruent _*_
    *-left-congruent {int px nx} {int py ny} {int pz nz} (z= py+nz=pz+ny) = z= (begin≅
        (px *N py ++ nx *N ny) ++ (px *N nz ++ nx *N pz)    ≅< <ab><cd>-to-<ac><bd>-on _++_ (px *N py) (nx *N ny) (px *N nz) (nx *N pz) >
        (px *N py ++ px *N nz) ++ (nx *N ny ++ nx *N pz)    ≅< bi-congruent _++_ (symmetric-on ℕ (left-distribute-on _*N_ _++_ px py nz)) (symmetric-on ℕ (left-distribute-on _*N_ _++_ nx ny pz)) >
        px *N (py ++ nz) ++ nx *N (ny ++ pz)                ≅< bi-congruent _++_ (left-congruent-on _*N_ {px} py+nz=pz+ny) (left-congruent-on _*N_ {nx} (commute-on _++_ ny pz)) >
        px *N (pz ++ ny) ++ nx *N (pz ++ ny)                ≅< left-congruent-on _++_ {px *N (pz ++ ny)} (left-congruent-on _*N_ {nx} (symmetric-on ℕ py+nz=pz+ny)) >
        px *N (pz ++ ny) ++ nx *N (py ++ nz)                ≅< left-congruent-on _++_ {px *N (pz ++ ny)} (left-congruent-on _*N_ {nx} (commute-on _++_ py nz)) >
        px *N (pz ++ ny) ++ nx *N (nz ++ py)                ≅< bi-congruent _++_ (left-distribute-on _*N_ _++_ px pz ny) (left-distribute-on _*N_ _++_ nx nz py) >
        (px *N pz ++ px *N ny) ++ (nx *N nz ++ nx *N py)    ≅< <ab><cd>-to-<ac><bd>-on _++_ (px *N pz) (px *N ny) (nx *N nz) (nx *N py) >
        (px *N pz ++ nx *N nz) ++ (px *N ny ++ nx *N py)    ∎)

    *-right-congruent : RightCongruent _*_
    *-right-congruent {int px nx} {int py ny} {int pz nz} (z= py+nz=pz+ny) = z= (begin≅
        (py *N px ++ ny *N nx) ++ (pz *N nx ++ nz *N px)    ≅< <ab><cd>-to-<ad><cb>-on _++_ (py *N px) (ny *N nx) (pz *N nx) (nz *N px) >
        (py *N px ++ nz *N px) ++ (pz *N nx ++ ny *N nx)    ≅< bi-congruent _++_ (symmetric-on ℕ (right-distribute-on _*N_ _++_ py nz px)) (symmetric-on ℕ (right-distribute-on _*N_ _++_ pz ny nx)) >
        (py ++ nz) *N px ++ (pz ++ ny) *N nx                ≅< bi-congruent _++_ (right-congruent-on _*N_ {px} py+nz=pz+ny) (right-congruent-on _*N_ {nx} (symmetric-on ℕ py+nz=pz+ny)) >
        (pz ++ ny) *N px ++ (py ++ nz) *N nx                ≅< bi-congruent _++_ (right-distribute-on _*N_ _++_ pz ny px) (right-distribute-on _*N_ _++_ py nz nx) >
        (pz *N px ++ ny *N px) ++ (py *N nx ++ nz *N nx)    ≅< <ab><cd>-to-<ad><cb>-on _++_ (pz *N px) (ny *N px) (py *N nx) (nz *N nx) >
        (pz *N px ++ nz *N nx) ++ (py *N nx ++ ny *N px)    ∎)

instance
    *-bi-congruent : BiCongruent _*_
    *-bi-congruent = record {left-congruent = *-left-congruent; right-congruent = *-right-congruent}

    *-magma : Magma _*_
    *-magma = record {}

private
    *-commute : Commute _*_
    *-commute (int px nx) (int py ny) = z= (begin≅
        (px *N py ++ nx *N ny) ++ (py *N nx ++ ny *N px)    ≅< bi-congruent _++_ (bi-congruent _++_ (commute-on _*N_ px py) (commute-on _*N_ nx ny)) (commute-on _++_ (py *N nx) (ny *N px)) >
        (py *N px ++ ny *N nx) ++ (ny *N px ++ py *N nx)    ≅< left-congruent-on _++_ {py *N px ++ ny *N nx} (bi-congruent _++_ (commute-on _*N_ ny px) (commute-on _*N_ py nx)) >
        (py *N px ++ ny *N nx) ++ (px *N ny ++ nx *N py)    ∎)

instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record {commute = *-commute}

    *-commutative-magma : CommutativeMagma _*_
    *-commutative-magma = record {}

private
    *-assoc : Associate _*_
    *-assoc (int px nx) (int py ny) (int pz nz) = z= (begin≅
        (px *N (py *N pz ++ ny *N nz) ++ nx *N (py *N nz ++ ny *N pz)) ++ ((px *N py ++ nx *N ny) *N nz ++ (px *N ny ++ nx *N py) *N pz)
                        ≅< bi-congruent _++_ 
                            (bi-congruent _++_
                                (left-distribute-on _*N_ _++_ px (py *N pz) (ny *N nz))
                                (left-distribute-on _*N_ _++_ nx (py *N nz) (ny *N pz)))
                            (bi-congruent _++_
                                (right-distribute-on _*N_ _++_ (px *N py) (nx *N ny) nz)
                                (right-distribute-on _*N_ _++_ (px *N ny) (nx *N py) pz)) >
        ((px *N (py *N pz) ++ px *N (ny *N nz)) ++ (nx *N (py *N nz) ++ nx *N (ny *N pz)))
            ++ (((px *N py) *N nz ++ (nx *N ny) *N nz) ++ ((px *N ny) *N pz ++ (nx *N py) *N pz))
                        ≅< bi-congruent _++_ 
                            (bi-congruent _++_
                                (bi-congruent _++_
                                    (left-associate-on _*N_ px py pz)
                                    (left-associate-on _*N_ px ny nz))
                                (bi-congruent _++_
                                    (left-associate-on _*N_ nx py nz)
                                    (left-associate-on _*N_ nx ny pz)))
                            (bi-congruent _++_
                                (bi-congruent _++_
                                    (right-associate-on _*N_ px py nz)
                                    (right-associate-on _*N_ nx ny nz))
                                (bi-congruent _++_
                                    (right-associate-on _*N_ px ny pz)
                                    (right-associate-on _*N_ nx py pz))) >
        (((px *N py) *N pz ++ (px *N ny) *N nz) ++ ((nx *N py) *N nz ++ (nx *N ny) *N pz))
            ++ ((px *N (py *N nz) ++ nx *N (ny *N nz)) ++ (px *N (ny *N pz) ++ nx *N (py *N pz)))
                        ≅< bi-congruent _++_
                            (<ab><cd>-to-<ad><bc>-on _++_ ((px *N py) *N pz) ((px *N ny) *N nz) ((nx *N py) *N nz) ((nx *N ny) *N pz))
                            (<ab><cd>-to-<ac><bd>-on _++_ (px *N (py *N nz)) (nx *N (ny *N nz)) (px *N (ny *N pz)) (nx *N (py *N pz))) >
        (((px *N py) *N pz ++ (nx *N ny) *N pz) ++ ((px *N ny) *N nz ++ (nx *N py) *N nz))
            ++ ((px *N (py *N nz) ++ px *N (ny *N pz)) ++ (nx *N (ny *N nz)) ++ nx *N (py *N pz))
                        ≅< symmetric-on ℕ (
                            bi-congruent _++_
                                (bi-congruent _++_
                                    (right-distribute-on _*N_ _++_ (px *N py) (nx *N ny) pz)
                                    (right-distribute-on _*N_ _++_ (px *N ny) (nx *N py) nz))
                                (bi-congruent _++_
                                    (left-distribute-on _*N_ _++_ px (py *N nz) (ny *N pz))
                                    (left-distribute-on _*N_ _++_ nx (ny *N nz) (py *N pz)))) >
        (((px *N py ++ nx *N ny) *N pz) ++ (px *N ny ++ nx *N py) *N nz)
            ++ (px *N (py *N nz ++ ny *N pz) ++ nx *N (ny *N nz ++ py *N pz))
                       ≅< left-congruent-on _++_ 
                            {((px *N py ++ nx *N ny) *N pz) ++ (px *N ny ++ nx *N py) *N nz}
                            (left-congruent-on _++_ 
                                {px *N (py *N nz ++ ny *N pz)} 
                                (left-congruent-on _*N_ 
                                    {nx} 
                                    (commute-on _++_ (ny *N nz) (py *N pz)))) >
        ((px *N py ++ nx *N ny) *N pz ++ (px *N ny ++ nx *N py) *N nz) ++ (px *N (py *N nz ++ ny *N pz) ++ nx *N (py *N pz ++ ny *N nz))
                        ∎)

instance
    *-is-associative : IsAssociative _*_
    *-is-associative = record {associate = *-assoc}

    *-semigroup : Semigroup _*_
    *-semigroup = record {}

    *-commutative-semigroup : CommutativeSemigroup _*_
    *-commutative-semigroup = record {}

private
    *-left-identity : LeftIdentity _*_ 1ℤ
    *-left-identity (int p n) = z= (begin≅
        (1ℕ *N p ++ 0ℕ *N n) ++ n       ≅< right-congruent-on _++_ (right-congruent-on _++_ (left-identity-on _*N_ p)) >
        (p ++ 0ℕ) ++ n                  ≅< bi-congruent _++_ (right-identity-on _++_ p) (symmetric-on ℕ (left-identity-on _*N_ n)) >
        p ++ (1ℕ *N n)                  ≅< left-congruent-on _++_ {p} (symmetric-on ℕ (right-identity-on _++_ (1ℕ *N n))) >
        p ++ (1ℕ *N n ++ 0ℕ)            ∎)

instance
    *-has-identity : HasIdentity _*_ 1ℤ
    *-has-identity = has-identity-commute *-left-identity

    *-monoid : Monoid _*_ 1ℤ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℤ
    *-commutative-monoid = record {}

private
    *-left-distributes : (x y z : ℤ) → x * (y + z) ≅ (x * y) + (x * z)
    *-left-distributes (int px nx) (int py ny) (int pz nz) = z= (begin≅
        (px *N (py ++ pz) ++ nx *N (ny ++ nz)) ++ ((px *N ny ++ nx *N py) ++ (px *N nz ++ nx *N pz))
                    ≅< bi-congruent _++_
                        (bi-congruent _++_
                            (left-distribute-on _*N_ _++_ px py pz)
                            (left-distribute-on _*N_ _++_ nx ny nz))
                        (<ab><cd>-to-<ac><bd>-on _++_
                            (px *N ny)
                            (nx *N py)
                            (px *N nz)
                            (nx *N pz)) >
        ((px *N py ++ px *N pz) ++ (nx *N ny ++ nx *N nz)) ++ ((px *N ny ++ px *N nz) ++ (nx *N py ++ nx *N pz))
                    ≅< bi-congruent _++_
                        (<ab><cd>-to-<ac><bd>-on _++_
                            (px *N py)
                            (px *N pz)
                            (nx *N ny)
                            (nx *N nz))
                        (symmetric-on ℕ
                            (bi-congruent _++_
                                (left-distribute-on _*N_ _++_ px ny nz)
                                (left-distribute-on _*N_ _++_ nx py pz))) >
        ((px *N py ++ nx *N ny) ++ (px *N pz ++ nx *N nz)) ++ (px *N (ny ++ nz) ++ nx *N (py ++ pz))
                    ∎)
    
    *-right-distributes : (x y z : ℤ) → (x + y) * z ≅ (x * z) + (y * z)
    *-right-distributes x y z = begin≅
        (x + y) * z     ≅< commute-on _*_ (x + y) z >
        z * (x + y)     ≅< *-left-distributes z x y >
        z * x + z * y   ≅< bi-congruent _+_ (commute-on _*_ z x) (commute-on _*_ z y) >
        x * z + y * z   ∎

instance
    *-+-ringoid : Ringoid _*_ _+_
    *-+-ringoid = record {left-distribute = *-left-distributes; right-distribute = *-right-distributes}

    *-+-ring : Ring _*_ _+_ 1ℤ 0ℤ neg
    *-+-ring = record {}

    *-+-semiring : Semiring _*_ _+_
    *-+-semiring = record {}

    *-+-commutative-ring : CommutativeRing _*_ _+_ 1ℤ 0ℤ neg
    *-+-commutative-ring = record {}

    *-zero : HasZero _*_ 0ℤ
    *-zero = Ring.zero *-+-ring

private
    integral-domain-lemma : (a b c d : ℕ) → (a *N c ++ b *N d) =N (a *N d ++ b *N c) → Either (a =N b) (c =N d)
    integral-domain-lemma a b c d eq with triΔ c d
    ... | tri= c=d      = right c=d
    ... | tri< n snc=d  = left (cancel-right-multiplication-nonzero {n} (right-injective-on _++_ (a *N c ++ b *N c) (begin≅
            a *N suc n ++ (a *N c ++ b *N c)    ≅< left-associate-on _++_ (a *N suc n) (a *N c) (b *N c) >
            (a *N suc n ++ a *N c) ++ b *N c    ≅< right-congruent-on _++_ (symmetric-on ℕ (left-distribute-on _*N_ _++_ a (suc n) c)) >
            a *N (suc n ++ c) ++ b *N c         ≅< right-congruent-on _++_ {b *N c} (left-congruent-on _*N_ {a} snc=d) >
            a *N d ++ b *N c                    ≅< symmetric-on ℕ eq >
            a *N c ++ b *N d                    ≅< left-congruent-on _++_ {a *N c} (left-congruent-on _*N_ {b} (symmetric-on ℕ snc=d)) >
            a *N c ++ b *N (suc n ++ c)         ≅< left-congruent-on _++_ (left-distribute-on _*N_ _++_ b (suc n) c) >
            a *N c ++ (b *N suc n ++ b *N c)    ≅< a<bc>-to-b<ac>-on _++_ (a *N c) (b *N suc n) (b *N c) >
            b *N suc n ++ (a *N c ++ b *N c)    ∎)))
    ... | tri> n snd=c = left (cancel-right-multiplication-nonzero {n} (right-injective-on _++_ (a *N d ++ b *N d) (begin≅
            a *N suc n ++ (a *N d ++ b *N d)    ≅< left-associate-on _++_ (a *N suc n) (a *N d) (b *N d) >
            (a *N suc n ++ a *N d) ++ b *N d    ≅< right-congruent-on _++_ (symmetric-on ℕ (left-distribute-on _*N_ _++_ a (suc n) d)) >
            a *N (suc n ++ d) ++ b *N d         ≅< right-congruent-on _++_ {b *N d} (left-congruent-on _*N_ {a} snd=c) >
            a *N c ++ b *N d                    ≅< eq >
            a *N d ++ b *N c                    ≅< left-congruent-on _++_ {a *N d} (left-congruent-on _*N_ {b} (symmetric-on ℕ snd=c)) >
            a *N d ++ b *N (suc n ++ d)         ≅< left-congruent-on _++_ {a *N d} (left-distribute-on _*N_ _++_ b (suc n) d) >
            a *N d ++ (b *N suc n ++ b *N d)    ≅< a<bc>-to-b<ac>-on _++_ (a *N d) (b *N suc n) (b *N d) >
            b *N suc n ++ (a *N d ++ b *N d)    ∎)))

    integral-domain : (x y : ℤ) → (x * y ≅ 0ℤ) → Either (x ≅ 0ℤ) (y ≅ 0ℤ)
    integral-domain (int a b) (int c d) (z= eq) with integral-domain-lemma a b c d (begin≅
        a *N c ++ b *N d            ≅< symmetric-on ℕ (right-identity-on _++_ (a *N c ++ b *N d)) >
        (a *N c ++ b *N d) ++ 0ℕ    ≅< eq >
        a *N d ++ b *N c            ∎)
    ... | left a=b = left (z= (begin≅
            a ++ 0ℕ     ≅< right-identity-on _++_ a >
            a           ≅< a=b >
            b           ∎))
    ... | right c=d = right (z= (begin≅
            c ++ 0ℕ     ≅< right-identity-on _++_ c >
            c           ≅< c=d >
            d           ∎))

instance
    ℤ-integral-domain : IntegralDomain _*_ _+_ 1ℤ 0ℤ neg
    ℤ-integral-domain = record {product-is-zero-one-is-zero = integral-domain}

private
    simplify-0≤ : {a b : ℕ} → 0ℤ ≤ int a b → b ≤N a
    simplify-0≤ {a} {b} (z≤ 0b≤a0) = bi-congruent-order _≤N_ (reflexive-on ℕ b) (symmetric-on ℕ (right-identity-on _++_ a)) 0b≤a0

    eq-to-eq0 : {a b : ℕ} → a =N b → int a b ≅ 0ℤ
    eq-to-eq0 {a} {b} a=b = z= (begin≅
        a ++ 0ℕ     ≅< commute-on _++_ a 0ℕ >
        0ℕ ++ a     ≅< left-congruent-on _++_ a=b >
        0ℕ ++ b     ∎)

{-*-nonnegative-preserves-order : (x y z : ℤ) → 0ℤ ≤ x → y ≤ z → x * y ≤ x * z
*-nonnegative-preserves-order (int a b) (int c d) (int e f) 0≤iab (z≤ ord2) = z≤ {! ord  !}
    where   b≤a = simplify-0≤ 0≤iab
-}

private
    nonnegative-to-ℕ : (x : ℤ) → 0ℤ ≤ x → Σ ℕ (λ n → x ≅ ℕ-to-ℤ n)
    nonnegative-to-ℕ (int p n) 0≤x with ordering-to-subtraction (simplify-0≤ 0≤x)
    ... | k , nk=p = k , z= (begin≅
            p ++ 0ℕ     ≅< right-identity-on _++_ p >
            p           ≅< symmetric-on ℕ nk=p >
            n ++ k  ≅< commute-on _++_ n k >
            k ++ n  ∎)

    positive-to-suc-ℕ : (x : ℤ) → 0ℤ ≤ x → ¬ (x ≅ 0ℤ) → Σ ℕ (λ n → x ≅ ℕ-to-ℤ (suc n))
    positive-to-suc-ℕ x 0≤x x≠0 with nonnegative-to-ℕ x 0≤x
    ... | 0ℕ , x=0      = contradiction-implies-anything (x≠0 x=0)
    ... | suc k , nsk=p = k , nsk=p

    cancel-right-multiplication-positive-≤-lemma : (x y : ℤ) (n : ℕ) → (x * ℕ-to-ℤ (suc n)) ≤ (y * ℕ-to-ℤ (suc n)) → x ≤ y
    cancel-right-multiplication-positive-≤-lemma (int px nx) (int py ny) n (z≤ xsn≤ysn) = 
        z≤  (cancel-right-multiplication-nonzero-≤ {px ++ ny} {py ++ nx} {n} 
                (bi-congruent-order _≤N_ 
                    (symmetric-on ℕ (begin≅
                        (px *N suc n ++ nx *N 0ℕ) ++ (py *N 0ℕ ++ ny *N suc n)      ≅< bi-congruent _++_ 
                                                                                            (left-congruent-on _++_ {px *N suc n} (right-zero-on _*N_ 0ℕ nx))
                                                                                            (right-congruent-on _++_ {ny *N suc n} (right-zero-on _*N_ 0ℕ py)) >
                        (px *N suc n ++ 0ℕ) ++ (ny *N suc n)                        ≅< right-congruent-on _++_ (right-identity-on _++_ (px *N suc n)) >
                        px *N suc n ++ ny *N suc n                                  ≅< symmetric-on ℕ (right-distribute-on _*N_ _++_ px ny (suc n)) >
                        (px ++ ny) *N suc n                                         ∎))
                    (symmetric-on ℕ (begin≅
                        (py *N suc n ++ ny *N 0ℕ) ++ (px *N 0ℕ ++ nx *N suc n)      ≅< bi-congruent _++_ 
                                                                                            (left-congruent-on _++_ {py *N suc n} (right-zero-on _*N_ 0ℕ ny))
                                                                                            (right-congruent-on _++_ {nx *N suc n} (right-zero-on _*N_ 0ℕ px)) >
                        (py *N suc n ++ 0ℕ) ++ (nx *N suc n)                        ≅< right-congruent-on _++_ (right-identity-on _++_ (py *N suc n)) >
                        py *N suc n ++ nx *N suc n                                  ≅< symmetric-on ℕ (right-distribute-on _*N_ _++_ py nx (suc n)) >
                        (py ++ nx) *N suc n                                         ∎))
                    xsn≤ysn))

cancel-right-multiplication-positive-≤ : (x y z : ℤ) → 0ℤ ≤ z → ¬ (z ≅ 0ℤ) → (x * z) ≤ (y * z) → x ≤ y
cancel-right-multiplication-positive-≤ (int px nx) (int py ny) z 0≤z z≠0 xz≤yz with positive-to-suc-ℕ z 0≤z z≠0
... | k , z=sk  = cancel-right-multiplication-positive-≤-lemma 
                        (int px nx) (int py ny) k 
                        (bi-congruent-order _≤_ (left-congruent-on _*_ (symmetric-on ℤ z=sk)) (left-congruent-on _*_ (symmetric-on ℤ z=sk)) xz≤yz)

cancel-left-multiplication-positive-≤ : (x y z : ℤ) → 0ℤ ≤ x → ¬ (x ≅ 0ℤ) → (x * y) ≤ (x * z) → y ≤ z
cancel-left-multiplication-positive-≤ x y z 0≤x x≠0 xy≤xz = 
    cancel-right-multiplication-positive-≤ y z x 0≤x x≠0 (bi-congruent-order _≤_ (commute-on _*_ y x) (commute-on _*_ z x) xy≤xz)

cancel-right-multiplication-negative-≤ : (x y z : ℤ) → z ≤ 0ℤ → ¬ (z ≅ 0ℤ) → (x * z) ≤ (y * z) → y ≤ x
cancel-right-multiplication-negative-≤ x y z z≤0 z≠0 xz≤yz = cancel-right-multiplication-positive-≤ y x (neg z) (neg-swaps-order z≤0) 
    (λ nz=0 → z≠0 (begin≅
        z               ≅< symmetric-on ℤ (neg-neg z) >
        neg (neg z)     ≅< congruent-on neg nz=0 >
        neg 0ℤ          ≅<>
        0ℤ              ∎))
    (bi-congruent-order _≤_ (right-times-neg-on _*_ _+_ 1ℤ 0ℤ neg y z) (right-times-neg-on _*_ _+_ 1ℤ 0ℤ neg x z) (neg-swaps-order xz≤yz))

cancel-left-multiplication-negative-≤ : (x y z : ℤ) → x ≤ 0ℤ → ¬ (x ≅ 0ℤ) → (x * y) ≤ (x * z) → z ≤ y
cancel-left-multiplication-negative-≤ x y z x≤0 x≠0 xy≤xz =
    cancel-right-multiplication-negative-≤ y z x x≤0 x≠0 (bi-congruent-order _≤_ (commute-on _*_ y x) (commute-on _*_ z x) xy≤xz)

left-multiplication-nonnegative : {x y z : ℤ} → 0ℤ ≤ x → y ≤ z → x * y ≤ x * z
left-multiplication-nonnegative {x} {int py ny} {int pz nz} 0≤x (z≤ py+nz≤pz+ny) with nonnegative-to-ℕ x 0≤x
... | n , x=n   = bi-congruent-order _≤_ (right-congruent-on _*_ x=n) (right-congruent-on _*_ x=n) 
        (z≤ (bi-congruent-order _≤N_ 
            (begin≅
                (n *N py ++ 0ℕ *N ny) ++ (n *N nz ++ 0ℕ *N pz)  ≅<>
                (n *N py ++ 0ℕ) ++ (n *N nz ++ 0ℕ)              ≅< bi-congruent _++_ (right-identity-on _++_ (n *N py)) (right-identity-on _++_ (n *N nz)) >
                n *N py ++ n *N nz                              ≅< symmetric-on ℕ (left-distribute-on _*N_ _++_ n py nz) >
                n *N (py ++ nz)                                 ∎) 
            (begin≅
                (n *N pz ++ 0ℕ *N nz) ++ (n *N ny ++ 0ℕ *N py)  ≅<>
                (n *N pz ++ 0ℕ) ++ (n *N ny ++ 0ℕ)              ≅< bi-congruent _++_ (right-identity-on _++_ (n *N pz)) (right-identity-on _++_ (n *N ny)) >
                n *N pz ++ n *N ny                              ≅< symmetric-on ℕ (left-distribute-on _*N_ _++_ n pz ny) >
                n *N (pz ++ ny)                                 ∎) 
            (multiplication-preserves-≤ (reflexive-order-on _≤N_ n) py+nz≤pz+ny)))

right-multiplication-nonnegative : {x y z : ℤ} → 0ℤ ≤ z → x ≤ y → x * z ≤ y * z
right-multiplication-nonnegative {x} {y} {z} 0≤z x≤y = bi-congruent-order _≤_ (commute-on _*_ x z) (commute-on _*_ y z) (left-multiplication-nonnegative 0≤z x≤y)

left-multiplication-negative : {x y z : ℤ} → x ≤ 0ℤ → y ≤ z → x * z ≤ x * y
left-multiplication-negative {x} {y} {z} x≤0 y≤z = bi-congruent-order _≤_ (lemma x z) (lemma x y) 
        (neg-swaps-order (left-multiplication-nonnegative {neg x} (neg-swaps-order x≤0) y≤z))
    where   lemma : (a b : ℤ) → (a * b) ≅ neg (neg a * b)
            lemma a b = symmetric-on ℤ (begin≅
                neg (neg a * b)     ≅< symmetric-on ℤ (right-times-neg-on _*_ _+_ 1ℤ 0ℤ neg (neg a) b) >
                neg a * neg b       ≅< neg-times-neg-on _*_ _+_ 1ℤ 0ℤ neg a b >
                a * b               ∎)

right-multiplication-negative : {x y z : ℤ} → z ≤ 0ℤ → x ≤ y → y * z ≤ x * z
right-multiplication-negative {x} {y} {z} z≤0 x≤y = bi-congruent-order _≤_ (commute-on _*_ y z) (commute-on _*_ x z) (left-multiplication-negative z≤0 x≤y)