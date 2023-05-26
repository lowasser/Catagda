module Definitions.Int.Addition where

open import Definitions.Int.Base
open import Definitions.Setoid
open import Definitions.Nat.Base renaming (_+_ to _++_; _≅_ to _=N_) hiding (+-bi-congruent; +-has-identity)
open import Definitions.Nat renaming (_≤_ to _≤N_) hiding (+-commutative-magma; +-commutative-semigroup; +-commutative-monoid)
open import Definitions.Function.Binary
open import Definitions.Setoid.Equation
open import Definitions.Semigroup.Commutative
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Group.Abelian

_+_ : BinOp ℤ
int px nx + int py ny = int (px ++ py) (nx ++ ny)

infixr 9 _+_

private
    +-right-congruent : {x y z : ℤ} → x ≅ y → x + z ≅ y + z
    +-right-congruent {int px nx} {int py ny} {int pz nz} (z= px+ny=py+nx) = z= (begin≅
        (px ++ pz) ++ (ny ++ nz)        ≅< <ab><cd>-to-<ac><bd>-on _++_ px pz ny nz >
        (px ++ ny) ++ (pz ++ nz)        ≅< right-congruent-on _++_ px+ny=py+nx >
        (py ++ nx) ++ (pz ++ nz)        ≅< <ab><cd>-to-<ac><bd>-on _++_ py nx pz nz >
        (py ++ pz) ++ (nx ++ nz)        ∎)

    +-left-congruent : {x y z : ℤ} → x ≅ y → z + x ≅ z + y
    +-left-congruent {int px nx} {int py ny} {int pz nz} (z= px+ny=py+nx) = z= (begin≅
        (pz ++ px) ++ (nz ++ ny)        ≅< <ab><cd>-to-<ac><bd>-on _++_ pz px nz ny >
        (pz ++ nz) ++ (px ++ ny)        ≅< left-congruent-on _++_ {pz ++ nz} px+ny=py+nx >
        (pz ++ nz) ++ (py ++ nx)        ≅< <ab><cd>-to-<ac><bd>-on _++_ pz nz py nx >
        (pz ++ py) ++ (nz ++ nx)        ∎)
    
instance
    +-bi-congruent : BiCongruent _+_
    +-bi-congruent = record { left-congruent = +-left-congruent; right-congruent = +-right-congruent }

    +-magma : Magma _+_
    +-magma = record {}

private
    +-commute : Commute _+_
    +-commute (int px nx) (int py ny) = z= (begin≅
        (px ++ py) ++ (ny ++ nx)    ≅< bi-congruent _++_ (commute-on _++_ px py) (commute-on _++_ ny nx) >
        (py ++ px) ++ (nx ++ ny)    ∎)

instance
    +-is-commutative : IsCommutative _+_
    +-is-commutative = record { commute = +-commute }

    +-commutative-magma : CommutativeMagma _+_
    +-commutative-magma = record {}

private    
    +-assoc : Associate _+_
    +-assoc (int px nx) (int py ny) (int pz nz) = z= (begin≅
        (px ++ (py ++ pz)) ++ ((nx ++ ny) ++ nz)    ≅< bi-congruent _++_ (left-associate-on _++_ px py pz) (right-associate-on _++_ nx ny nz) >
        ((px ++ py) ++ pz) ++ (nx ++ (ny ++ nz))    ∎)

instance
    +-is-associative : IsAssociative _+_
    +-is-associative = record { associate = +-assoc }

    +-semigroup : Semigroup _+_
    +-semigroup = record {}

    +-commutative-semigroup : CommutativeSemigroup _+_
    +-commutative-semigroup = record {}

private
    +-left-id : LeftIdentity _+_ 0ℤ
    +-left-id (int px nx) = z= (bi-congruent _++_ (left-identity-on _++_ px) (symmetric-on ℕ (left-identity-on _++_ nx)))

instance
    +-has-identity : HasIdentity _+_ 0ℤ
    +-has-identity = has-identity-commute +-left-id

    +-monoid : Monoid _+_ 0ℤ
    +-monoid = record {}

    +-commutative-monoid : CommutativeMonoid _+_ 0ℤ
    +-commutative-monoid = record {}

private
    neg-left-inverse : LeftInverse _+_ 0ℤ neg
    neg-left-inverse (int p n) = z= (begin≅
        (n ++ p) ++ 0ℕ      ≅< right-identity-on _++_ (n ++ p) >
        n ++ p              ≅< commute-on _++_ n p >
        p ++ n              ∎)

instance
    +-has-inverse : HasInverse _+_ 0ℤ neg
    +-has-inverse = has-inverse-commute neg-left-inverse

    +-group : Group _+_ 0ℤ neg
    +-group = record {}

    +-abelian-group : AbelianGroup _+_ 0ℤ neg
    +-abelian-group = record {}