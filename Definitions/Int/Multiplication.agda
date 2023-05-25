module Definitions.Int.Multiplication where

open import Agda.Primitive
open import Definitions.Nat
    hiding (*-magma; *-is-commutative; *-commutative-magma; *-is-associative; *-semigroup; *-commutative-semigroup; *-has-identity; *-monoid; *-commutative-monoid; *-ringoid)
    renaming (_+_ to _++_; _≅_ to _=N_; _*_ to _*N_)
open import Definitions.Int.Base
open import Definitions.Int.Addition
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Semigroup.Commutative
open import Definitions.Ringoid
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Ring
open import Definitions.Ring.Semi
open import Definitions.Ring.Commutative

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
    *-+-ringoid : Ringoid _+_ _*_
    *-+-ringoid = record {left-distribute = *-left-distributes; right-distribute = *-right-distributes}

    *-+-ring : Ring _+_ _*_ 0ℤ 1ℤ neg
    *-+-ring = record {}

    *-+-semiring : Semiring _+_ _*_
    *-+-semiring = record {}

    *-+-commutative-ring : CommutativeRing _+_ _*_ 0ℤ 1ℤ neg
    *-+-commutative-ring = record {}