module Data.Number.Int.Addition where

open import Data.Number.Int.Base
open import Agda.Builtin.Sigma
open import Structure.Setoid
open import Data.Number.Nat.Base renaming (_≅_ to _=N_)
open import Data.Number.Nat.Addition renaming (_+_ to _++_) hiding (+-bi-congruent; +-has-identity; +-commutative-magma; +-commutative-semigroup; +-commutative-monoid)
open import Data.Number.Nat.Order renaming (_≤_ to _≤N_)
open import Data.Number.Int.Order
open import Function.Binary
open import Structure.Setoid.Equation
open import Structure.Algebraic.Semigroup.Commutative
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Group
open import Structure.Algebraic.Group.Abelian
open import Relation.Order.Partial

_+_ : BinOp ℤ
int px nx + int py ny = int (px ++ py) (nx ++ ny)

infixr 9 _+_

neg : ℤ → ℤ
neg (int p n) = int n p

private
    +-left-congruent : {x y z : ℤ} → x ≅ y → z + x ≅ z + y
    +-left-congruent {int px nx} {int py ny} {int pz nz} (z= px+ny=py+nx) = z= (begin≅
        (pz ++ px) ++ (nz ++ ny)        ≅< <ab><cd>-to-<ac><bd>-on _++_ pz px nz ny >
        (pz ++ nz) ++ (px ++ ny)        ≅< left-congruent-on _++_ {pz ++ nz} px+ny=py+nx >
        (pz ++ nz) ++ (py ++ nx)        ≅< <ab><cd>-to-<ac><bd>-on _++_ pz nz py nx >
        (pz ++ py) ++ (nz ++ nx)        ∎)
    
    +-commute : Commute _+_
    +-commute (int px nx) (int py ny) = z= (begin≅
        (px ++ py) ++ (ny ++ nx)    ≅< bi-congruent _++_ (commute-on _++_ px py) (commute-on _++_ ny nx) >
        (py ++ px) ++ (nx ++ ny)    ∎)

    +-assoc : Associate _+_
    +-assoc (int px nx) (int py ny) (int pz nz) = z= (begin≅
        (px ++ (py ++ pz)) ++ ((nx ++ ny) ++ nz)    ≅< bi-congruent _++_ (left-associate-on _++_ px py pz) (right-associate-on _++_ nx ny nz) >
        ((px ++ py) ++ pz) ++ (nx ++ (ny ++ nz))    ∎)

    +-left-id : LeftIdentity _+_ 0ℤ
    +-left-id (int px nx) = z= (bi-congruent _++_ (left-identity-on _++_ px) (symmetric-on ℕ (left-identity-on _++_ nx)))

    neg-left-inverse : (x : ℤ) → neg x + x ≅ 0ℤ
    neg-left-inverse (int p n) = z= (begin≅
        (n ++ p) ++ 0ℕ      ≅< right-identity-on _++_ (n ++ p) >
        n ++ p              ≅< commute-on _++_ n p >
        p ++ n              ∎)

    neg-congruent : Congruent neg
    neg-congruent {int px nx} {int py ny} (z= px+ny=py+nx) = z= (begin≅
        nx ++ py        ≅< commute-on _++_ nx py >
        py ++ nx        ≅< symmetric-on ℕ px+ny=py+nx >
        px ++ ny        ≅< commute-on _++_ px ny >
        ny ++ px        ∎)

open import Structure.Algebraic.Group.Abelian.Instance _+_ 0ℤ neg +-left-congruent +-commute +-assoc +-left-id neg-congruent neg-left-inverse public

neg-neg : (x : ℤ) → neg (neg x) ≅ x
neg-neg (int p n) = reflexive-on ℤ (int p n)

data PosNegℤ : Set where
    nonneg : ℕ → PosNegℤ
    negsuc : ℕ → PosNegℤ

posnegℤ-to-ℤ : PosNegℤ → ℤ
posnegℤ-to-ℤ (nonneg n) = ℕ-to-ℤ n
posnegℤ-to-ℤ (negsuc n) = neg (ℕ-to-ℤ (suc n))

private
    sub-both : (p n : ℕ) → int (suc p) (suc n) ≅ int p n
    sub-both p n = z= (begin≅
        suc p ++ n      ≅<>
        (1ℕ ++ p) ++ n  ≅< right-congruent-on _++_ (commute-on _++_ 1ℕ p) >
        (p ++ 1ℕ) ++ n  ≅< right-associate-on _++_ p 1ℕ n >
        p ++ suc n      ∎)

canonicalize : (x : ℤ) → Σ PosNegℤ (λ pnz → x ≅ posnegℤ-to-ℤ pnz)
canonicalize (int n 0ℕ) = nonneg n , reflexive-on ℤ (int n 0ℕ)
canonicalize (int 0ℕ (suc n)) = negsuc n , reflexive-on ℤ (int 0ℕ (suc n))
canonicalize (int (suc p) (suc n)) with canonicalize (int p n)
... | pnz , eq  = pnz , transitive-on ℤ (sub-both p n) eq

absℕ : ℤ → ℕ
absℕ (int 0ℕ b) = b
absℕ (int a 0ℕ) = a
absℕ (int (suc a) (suc b)) = absℕ (int a b)

abs : ℤ → ℤ
abs (int a b) = int (max a b) (min a b)

abs=ℕ : (x : ℤ) → ℕ-to-ℤ (absℕ x) ≅ abs x
abs=ℕ (int 0ℕ b) = z= (begin≅
    absℕ (int 0ℕ b) ++ min 0ℕ b     ≅<>
    b ++ 0ℕ                         ≅< right-congruent-on _++_ (symmetric-on ℕ (left-identity-on max b)) >
    max 0ℕ b ++ 0ℕ                  ∎)
abs=ℕ (int (suc a) 0ℕ) = z= (begin≅
    absℕ (ℕ-to-ℤ (suc a)) ++ min (suc a) 0ℕ     ≅<>
    suc a ++ min (suc a) 0ℕ                     ≅< left-congruent-on _++_ (right-zero-on min 0ℕ (suc a)) >
    max (suc a) 0ℕ ++ 0ℕ                        ∎)
abs=ℕ (int (suc a) (suc b)) with abs=ℕ (int a b)
... | z= absab+minab=maxab+0 = z= (begin≅
        absℕ (int a b) ++ suc (min a b)     ≅< a<bc>-to-b<ac>-on _++_ (absℕ (int a b)) 1ℕ (min a b) >
        suc (absℕ (int a b) ++ min a b)     ≅< congruent-on suc absab+minab=maxab+0 >
        suc (max a b) ++ 0ℕ                 ∎)

abs=neg : (x : ℤ) → abs x ≅ abs (neg x)
abs=neg (int p q) = z= (bi-congruent _++_ (commute-on max p q) (commute-on min q p))

left-+-preserves-≤ : (a : ℤ) → {b c : ℤ} → b ≤ c → a + b ≤ a + c
left-+-preserves-≤ (int pa na) {int pb nb} {int pc nc} (z≤ pbnc≤pcnb) = z≤ 
    (bi-congruent-order _≤N_ 
        (<ab><cd>-to-<ac><bd>-on _++_ pa pb na nc) 
        (<ab><cd>-to-<ac><bd>-on _++_ pa pc na nb) 
        (addition-preserves-≤ (reflexive-order-on _≤N_ (pa ++ na)) pbnc≤pcnb))

neg-swaps-order : {x y : ℤ} → x ≤ y → neg y ≤ neg x
neg-swaps-order {int px nx} {int py ny} (z≤ pxny≤pynx) = z≤ (bi-congruent-order _≤N_ (commute-on _++_ ny px) (commute-on _++_ nx py) pxny≤pynx)