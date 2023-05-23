module Definitions.Int.Ordering where

open import Definitions.Int.Base
open import Definitions.Int.Addition
open import Definitions.Nat renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_; suc to sucℕ)
open import Definitions.Pair
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Definitions.List.Setoid {lzero} {lzero} ⊤ renaming (cons=[]=cons to consℕ)
open import Definitions.Group.Free {lzero} {lzero} ⊤
open import Agda.Builtin.Sigma
open import Definitions.Setoid
open import Definitions.Relation.Equivalence.Structural renaming (refl to ≡-refl)
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.List 
open import Definitions.Setoid.Equation
open import Definitions.Function.Binary.Properties
open import Definitions.Either
open import Definitions.Group
open import Definitions.Relation
open import Definitions.Relation.Order.Total
open import Definitions.Relation.Equivalence.Structural.Properties Ordering
open import Definitions.Either.Setoid {lzero} {lzero} {lzero} {lzero} ⊤ ⊤
open import Definitions.List.Setoid {lzero} {lzero} (Either ⊤ ⊤)
open import Definitions.Relation
open import Definitions.Semigroup.Commutative 
open import Definitions.Relation.Properties
open import Definitions.Relation.Order.Partial
open import Definitions.List.Concatenation.Properties {lzero} {lzero} ⊤

open CommutativeSemigroup {{...}}

private
    Letter Word : Set
    Letter = Either ⊤ ⊤
    Word = [ Letter ]

    _≅ℕ_ : {{SN : Setoid lzero ℕ}} → Rel lzero ℕ
    _≅ℕ_ {{SN}} = _≅_
        where open Setoid SN
        
    open Setoid {{...}}

    count-pos-word count-neg-word : Word → ℕ
    count-pos-word [] = 0ℕ
    count-pos-word (p1 :: x) = sucℕ (count-pos-word x)
    count-pos-word (m1 :: x) = count-pos-word x

    count-neg-word [] = 0ℕ
    count-neg-word (p1 :: x) = count-neg-word x
    count-neg-word (m1 :: x) = sucℕ (count-neg-word x)

    count-pos-word-congruent : (x y : Word) → x ≅ y → count-pos-word x ≅ℕ count-pos-word y
    count-pos-word-congruent _ _ []=[] = reflexive-on ℕ 0ℕ
    count-pos-word-congruent (p1 :: x) (p1 :: y) (cons=[]=cons _ x=y) = consℕ ≡-refl (count-pos-word-congruent x y x=y)
    count-pos-word-congruent (m1 :: x) (m1 :: y) (cons=[]=cons _ x=y) = count-pos-word-congruent x y x=y

    count-neg-word-congruent : (x y : Word) → x ≅ y → count-neg-word x ≅ count-neg-word y
    count-neg-word-congruent _ _ []=[] = reflexive-on ℕ 0ℕ
    count-neg-word-congruent (p1 :: x) (p1 :: y) (cons=[]=cons _ x=y) = count-neg-word-congruent x y x=y
    count-neg-word-congruent (m1 :: x) (m1 :: y) (cons=[]=cons _ x=y) = consℕ ≡-refl (count-neg-word-congruent x y x=y)

    count-pos count-neg : ℤ → ℕ
    count-pos (free x) = count-pos-word x
    count-neg (free x) = count-neg-word x

    data _≤W_ : Rel lzero Word where
        wle : (x y : Word) → count-pos-word x +ℕ count-neg-word y ≤ℕ count-pos-word y +ℕ count-neg-word x → x ≤W y

    open PreOrder {{...}}

    count-pos-insert-m1 : (x1 x2 : Word) → count-pos-word (x1 ++ m1 :: x2) ≅ℕ count-pos-word (x1 ++ x2)
    count-pos-insert-m1 [] x2 = reflexive-on ℕ (count-pos-word x2)
    count-pos-insert-m1 (p1 :: x1) x2 = consℕ ≡-refl (count-pos-insert-m1 x1 x2)
    count-pos-insert-m1 (m1 :: x1) x2 = count-pos-insert-m1 x1 x2

    count-pos-insert-p1 : (x1 x2 : Word) → count-pos-word (x1 ++ p1 :: x2) ≅ℕ sucℕ (count-pos-word (x1 ++ x2))
    count-pos-insert-p1 [] x2 = reflexive-on ℕ (sucℕ (count-pos-word x2))
    count-pos-insert-p1 (p1 :: x1) x2 = consℕ ≡-refl (count-pos-insert-p1 x1 x2)
    count-pos-insert-p1 (m1 :: x1) x2 = count-pos-insert-p1 x1 x2

    count-neg-insert-p1 : (x1 x2 : Word) → count-neg-word (x1 ++ p1 :: x2) ≅ℕ count-neg-word (x1 ++ x2)
    count-neg-insert-p1 [] x2 = reflexive-on ℕ (count-neg-word x2)
    count-neg-insert-p1 (p1 :: x1) x2 = count-neg-insert-p1 x1 x2
    count-neg-insert-p1 (m1 :: x1) x2 = consℕ ≡-refl (count-neg-insert-p1 x1 x2)

    count-neg-insert-m1 : (x1 x2 : Word) → count-neg-word (x1 ++ m1 :: x2) ≅ℕ sucℕ (count-neg-word (x1 ++ x2))
    count-neg-insert-m1 [] x2 = reflexive-on ℕ (sucℕ (count-neg-word x2))
    count-neg-insert-m1 (p1 :: x1) x2 = count-neg-insert-m1 x1 x2
    count-neg-insert-m1 (m1 :: x1) x2 = consℕ ≡-refl (count-neg-insert-m1 x1 x2)

    ≤W-transitive : {x y z : Word} → x ≤W y → y ≤W z → x ≤W z
    ≤W-transitive (wle x y px+ny≤py+nx) (wle y z py+nz≤pz+ny) = wle x z 
            (subtract-both-≤ 
                (py +ℕ ny) 
                (px +ℕ nz) 
                (pz +ℕ nx) 
                (bi-congruent-order _≤ℕ_ 
                    (begin≅
                        (py +ℕ ny) +ℕ (px +ℕ nz)    ≅< right-associate-on _+ℕ_ py ny (px +ℕ nz) >
                        py +ℕ (ny +ℕ (px +ℕ nz))    ≅< left-congruent-on _+ℕ_ {py} (left-associate-on _+ℕ_ ny px nz) >
                        py +ℕ ((ny +ℕ px) +ℕ nz)    ≅< commute-on _+ℕ_ py ((ny +ℕ px) +ℕ nz) >
                        ((ny +ℕ px) +ℕ nz) +ℕ py    ≅< right-associate-on _+ℕ_ (ny +ℕ px) nz py >
                        (ny +ℕ px) +ℕ (nz +ℕ py)    ≅< bi-congruent _+ℕ_ (commute-on _+ℕ_ ny px) (commute-on _+ℕ_ nz py) >
                        (px +ℕ ny) +ℕ (py +ℕ nz)    ∎)
                    (begin≅
                        (py +ℕ ny) +ℕ (pz +ℕ nx)    ≅< right-associate-on _+ℕ_ py ny (pz +ℕ nx) >
                        py +ℕ (ny +ℕ (pz +ℕ nx))    ≅< left-congruent-on _+ℕ_ {py} (left-associate-on _+ℕ_ ny pz nx) >
                        py +ℕ ((ny +ℕ pz) +ℕ nx)    ≅< left-congruent-on _+ℕ_ {py} (commute-on _+ℕ_ (ny +ℕ pz) nx) >
                        py +ℕ (nx +ℕ (ny +ℕ pz))    ≅< left-associate-on _+ℕ_ py nx (ny +ℕ pz) >
                        (py +ℕ nx) +ℕ (ny +ℕ pz)    ≅< left-congruent-on _+ℕ_ {py +ℕ nx} (commute-on _+ℕ_ ny pz) >
                        (py +ℕ nx) +ℕ (pz +ℕ ny)    ∎)
                    (addition-preserves-≤ px+ny≤py+nx py+nz≤pz+ny)))
        where   px = count-pos-word x
                py = count-pos-word y
                pz = count-pos-word z
                nx = count-neg-word x
                ny = count-neg-word y
                nz = count-neg-word z

    count-equality-word : {x y : Word} → EqClosure x y → (count-pos-word x +ℕ count-neg-word y) ≅ℕ (count-pos-word y +ℕ count-neg-word x)
    count-equality-word (sym y=x) = symmetric-on ℕ (count-equality-word y=x)
    count-equality-word (trans {x} {z} {y} x=z z=y) = left-injective-on _+ℕ_ (pz ++ nz) (begin≅
                (pz ++ nz) ++ (px ++ ny)        ≅< left-associate-on _++_ (pz ++ nz) px ny >
                ((pz ++ nz) ++ px) ++ ny        ≅< commute-on _++_ ((pz ++ nz) ++ px) ny >
                ny ++ ((pz ++ nz) ++ px)        ≅< left-congruent-on _++_ {ny} (right-associate-on _++_ pz nz px) >
                ny ++ (pz ++ (nz ++ px))        ≅< left-associate-on _++_ ny pz (nz ++ px) >
                (ny ++ pz) ++ (nz ++ px)        ≅< bi-congruent _++_ (commute-on _++_ ny pz) (commute-on _++_ nz px) >
                (pz ++ ny) ++ (px ++ nz)        ≅< bi-congruent _++_ (count-equality-word z=y) (count-equality-word x=z) >
                (py ++ nz) ++ (pz ++ nx)        ≅< bi-congruent _++_ (commute-on _++_ py nz) (commute-on _++_ pz nx) >
                (nz ++ py) ++ (nx ++ pz)        ≅< right-associate-on _++_ nz py (nx ++ pz) >
                nz ++ (py ++ (nx ++ pz))        ≅< left-congruent-on _++_ {nz} (left-associate-on _++_ py nx pz) >
                nz ++ ((py ++ nx) ++ pz)        ≅< left-congruent-on _++_ {nz} (commute-on _++_ (py ++ nx) pz) >
                nz ++ (pz ++ (py ++ nx))        ≅< left-associate-on _++_ nz pz (py ++ nx) >
                (nz ++ pz) ++ (py ++ nx)        ≅< right-congruent-on _++_ (commute-on _++_ nz pz) >
                (pz ++ nz) ++ (py ++ nx)        ∎)
            where   px = count-pos-word x
                    py = count-pos-word y
                    pz = count-pos-word z
                    nx = count-neg-word x
                    ny = count-neg-word y
                    nz = count-neg-word z
    count-equality-word (refl x y x=y) = begin≅
        count-pos-word x ++ count-neg-word y    ≅< bi-congruent _++_ (count-pos-word-congruent x y x=y) (count-neg-word-congruent y x (symmetric-on Word x=y)) >
        count-pos-word y ++ count-neg-word x    ∎
    count-equality-word (imp (reduces x1 p1 x2)) = begin≅
        count-pos-word (x1 ++ m1 :: p1 :: x2) ++ count-neg-word (x1 ++ x2)  ≅< right-congruent-on _++_ (count-pos-insert-m1 x1 (p1 :: x2)) >
        count-pos-word (x1 ++ p1 :: x2) ++ count-neg-word (x1 ++ x2)        ≅< right-congruent-on _++_ (count-pos-insert-p1 x1 x2) >
        (1ℕ ++ count-pos-word (x1 ++ x2)) ++ count-neg-word (x1 ++ x2)      ≅< right-congruent-on _++_ (commute-on _++_ 1ℕ (count-pos-word (x1 ++ x2))) >
        (count-pos-word (x1 ++ x2) ++ 1ℕ) ++ count-neg-word (x1 ++ x2)      ≅< right-associate-on _++_ (count-pos-word (x1 ++ x2)) 1ℕ (count-neg-word (x1 ++ x2)) >
        count-pos-word (x1 ++ x2) ++ (1ℕ ++ count-neg-word (x1 ++ x2))      ≅< left-congruent-on _++_ (left-congruent-on _++_ {1ℕ} (symmetric-on ℕ (count-neg-insert-p1 x1 x2))) >
        count-pos-word (x1 ++ x2) ++ sucℕ (count-neg-word (x1 ++ p1 :: x2)) ≅< left-congruent-on _++_ (symmetric-on ℕ (count-neg-insert-m1 x1 (p1 :: x2))) >
        count-pos-word (x1 ++ x2) ++ count-neg-word (x1 ++ m1 :: p1 :: x2)  ∎
    count-equality-word (imp (reduces x1 m1 x2)) = begin≅
        count-pos-word (x1 ++ p1 :: m1 :: x2) ++ count-neg-word (x1 ++ x2)  ≅< right-congruent-on _++_ (count-pos-insert-p1 x1 (m1 :: x2)) >
        (1ℕ ++ count-pos-word (x1 ++ m1 :: x2)) ++ count-neg-word (x1 ++ x2) ≅< right-congruent-on _++_ (left-congruent-on _++_ {1ℕ} (count-pos-insert-m1 x1 x2)) >
        (1ℕ ++ count-pos-word (x1 ++ x2)) ++ count-neg-word (x1 ++ x2)      ≅< right-congruent-on _++_ (commute-on _++_ 1ℕ (count-pos-word (x1 ++ x2))) >
        (count-pos-word (x1 ++ x2) ++ 1ℕ) ++ count-neg-word (x1 ++ x2)      ≅< right-associate-on _++_ (count-pos-word (x1 ++ x2)) 1ℕ (count-neg-word (x1 ++ x2)) >
        count-pos-word (x1 ++ x2) ++ (1ℕ ++ count-neg-word (x1 ++ x2))      ≅< left-congruent-on _++_ (symmetric-on ℕ (count-neg-insert-m1 x1 x2)) >
        count-pos-word (x1 ++ x2) ++ count-neg-word (x1 ++ m1 :: x2)        ≅< left-congruent-on _++_ (symmetric-on ℕ (count-neg-insert-p1 x1 (m1 :: x2))) >
        count-pos-word (x1 ++ x2) ++ count-neg-word (x1 ++ p1 :: m1 :: x2)  ∎

    count-equality : (x y : ℤ) → x ≅ y → (count-pos x +ℕ count-neg y) ≅ℕ (count-pos y +ℕ count-neg x)
    count-equality (free x) (free y) (eqfg x=y) = count-equality-word x=y

    ≤W-reflexive : (x y : Word) → EqClosure x y → x ≤W y
    ≤W-reflexive x y x=y = wle x y (reflexive-equiv-order-on _≤ℕ_ (count-equality-word x=y))

    ≤W-left-congruent : {x y z : Word} → EqClosure x y → y ≤W z → x ≤W z
    ≤W-left-congruent {x} {y} {z} x=y (wle y z y≤z) = wle x z 
        (subtract-both-≤ (py ++ ny) (px ++ nz) (pz ++ nx) 
            (bi-congruent-order _≤ℕ_ 
                (begin≅
                        (py ++ ny) ++ (px ++ nz)        ≅< left-associate-on _++_ (py ++ ny) px nz >
                        ((py ++ ny) ++ px) ++ nz        ≅< right-congruent-on _++_ (right-associate-on _++_ py ny px) >
                        (py ++ (ny ++ px)) ++ nz        ≅< right-congruent-on _++_ (commute-on _++_ py (ny ++ px)) >
                        ((ny ++ px) ++ py) ++ nz        ≅< right-associate-on _++_ (ny ++ px) py nz >
                        (ny ++ px) ++ (py ++ nz)        ≅< right-congruent-on _++_ (commute-on _++_ ny px) >
                        (px ++ ny) ++ (py ++ nz)        ∎)
                (begin≅
                        (py ++ ny) ++ (pz ++ nx)        ≅< left-associate-on _++_ (py ++ ny) pz nx >
                        ((py ++ ny) ++ pz) ++ nx        ≅< right-congruent-on _++_ (right-associate-on _++_ py ny pz) >
                        (py ++ (ny ++ pz)) ++ nx        ≅< right-congruent-on _++_ (commute-on _++_ py (ny ++ pz)) >
                        ((ny ++ pz) ++ py) ++ nx        ≅< right-associate-on _++_ (ny ++ pz) py nx >
                        (ny ++ pz) ++ (py ++ nx)        ≅< right-congruent-on _++_ (commute-on _++_ ny pz) >
                        (pz ++ ny) ++ (py ++ nx)        ≅< commute-on _++_ (pz ++ ny) (py ++ nx) >
                        (py ++ nx) ++ (pz ++ ny)        ∎)
                (addition-preserves-≤ (reflexive-equiv-order-on _≤ℕ_ (count-equality-word x=y)) y≤z)))
        where   px = count-pos-word x
                py = count-pos-word y
                pz = count-pos-word z
                nx = count-neg-word x 
                ny = count-neg-word y
                nz = count-neg-word z 
 
    ≤W-right-congruent : {x y z : Word} → EqClosure y z → x ≤W y → x ≤W z
    ≤W-right-congruent {x} {y} {z} y=z (wle x y x≤y) = wle x z 
        (subtract-both-≤ (py ++ ny) (px ++ nz) (pz ++ nx) 
            (bi-congruent-order _≤ℕ_ 
                (begin≅
                        (py ++ ny) ++ (px ++ nz)        ≅< left-associate-on _++_ (py ++ ny) px nz >
                        ((py ++ ny) ++ px) ++ nz        ≅< right-congruent-on _++_ (right-associate-on _++_ py ny px) >
                        (py ++ (ny ++ px)) ++ nz        ≅< right-congruent-on _++_ (commute-on _++_ py (ny ++ px)) >
                        ((ny ++ px) ++ py) ++ nz        ≅< right-associate-on _++_ (ny ++ px) py nz >
                        (ny ++ px) ++ (py ++ nz)        ≅< right-congruent-on _++_ (commute-on _++_ ny px) >
                        (px ++ ny) ++ (py ++ nz)        ∎)
                (begin≅
                        (py ++ ny) ++ (pz ++ nx)        ≅< left-associate-on _++_ (py ++ ny) pz nx >
                        ((py ++ ny) ++ pz) ++ nx        ≅< right-congruent-on _++_ (right-associate-on _++_ py ny pz) >
                        (py ++ (ny ++ pz)) ++ nx        ≅< right-congruent-on _++_ (commute-on _++_ py (ny ++ pz)) >
                        ((ny ++ pz) ++ py) ++ nx        ≅< right-associate-on _++_ (ny ++ pz) py nx >
                        (ny ++ pz) ++ (py ++ nx)        ≅< right-congruent-on _++_ (commute-on _++_ ny pz) >
                        (pz ++ ny) ++ (py ++ nx)        ≅< commute-on _++_ (pz ++ ny) (py ++ nx) >
                        (py ++ nx) ++ (pz ++ ny)        ∎)
                (addition-preserves-≤ x≤y (reflexive-equiv-order-on _≤ℕ_ (count-equality-word y=z)))))
        where   px = count-pos-word x
                py = count-pos-word y
                pz = count-pos-word z
                nx = count-neg-word x 
                ny = count-neg-word y
                nz = count-neg-word z
    
    record WithoutP1 (x : Word) (y : Word) : Set where
        field
            without-p1-eq : free x ≅ free (p1 :: y)
            count-pos-suc : count-pos-word x ≅ℕ sucℕ (count-pos-word y)
            count-neg-eq : count-neg-word x ≅ℕ count-neg-word y

    inc-wp1-m1 : {x y : Word} → WithoutP1 x y → WithoutP1 (m1 :: x) (m1 :: y)
    inc-wp1-m1 {x} {y} wp1 = record {
            without-p1-eq = begin≅
                free (m1 :: x)          ≅<>
                -1ℤ + free x            ≅< left-congruent-on _+_ without-p1-eq >
                -1ℤ + free (p1 :: y)    ≅<>
                -1ℤ + (1ℤ + free y)     ≅< left-associate-on _+_ -1ℤ 1ℤ (free y) >
                (-1ℤ + 1ℤ) + free y     ≅< right-congruent-on _+_ (commute-on _+_ -1ℤ 1ℤ) >
                (1ℤ + -1ℤ) + free y     ≅<>
                free (p1 :: m1 :: y)    ∎;
            count-pos-suc = count-pos-suc;
            count-neg-eq = begin≅
                count-neg-word (m1 :: x)        ≅<>
                sucℕ (count-neg-word x)         ≅< suc= count-neg-eq >
                sucℕ (count-neg-word y)         ≅<>
                count-neg-word (m1 :: y)        ∎}
        where open WithoutP1 wp1

    pos-to-front : (x : Word) → Either (Σ Word (WithoutP1 x)) (count-pos-word x ≅ℕ 0ℕ)
    pos-to-front [] = right (reflexive-on ℕ 0ℕ)
    pos-to-front (p1 :: x) = left (x , record { 
        without-p1-eq = reflexive-on ℤ (free (p1 :: x));
        count-pos-suc = begin≅
            count-pos-word (p1 :: x)    ≅<>
            sucℕ (count-pos-word x)     ∎;
        count-neg-eq = reflexive-on ℕ (count-neg-word x) })
    pos-to-front (m1 :: x) with pos-to-front x
    ... | left (y , wp1y)   = left (m1 :: y , inc-wp1-m1 wp1y)
    ... | right cpx=0       = right cpx=0

    record WithoutM1 (x : Word) (y : Word) : Set where
        field
            without-m1-eq : free x ≅ free (m1 :: y)
            count-pos-eq : count-pos-word x ≅ℕ count-pos-word y
            count-neg-suc : count-neg-word x ≅ℕ sucℕ (count-neg-word y)

    inc-wm1-p1 : {x y : Word} → WithoutM1 x y → WithoutM1 (p1 :: x) (p1 :: y)
    inc-wm1-p1 {x} {y} wm1 = record {
            without-m1-eq = begin≅
                free (p1 :: x)          ≅<>
                1ℤ + free x             ≅< left-congruent-on _+_ without-m1-eq >
                1ℤ + free (m1 :: y)     ≅<>
                1ℤ + (-1ℤ + free y)     ≅< left-associate-on _+_ 1ℤ -1ℤ (free y) >
                (1ℤ + -1ℤ) + free y     ≅< right-congruent-on _+_ (commute-on _+_ 1ℤ -1ℤ) >
                (-1ℤ + 1ℤ) + free y     ≅<>
                free (m1 :: p1 :: y)    ∎;
            count-neg-suc = count-neg-suc;
            count-pos-eq = begin≅
                count-pos-word (p1 :: x)        ≅<>
                sucℕ (count-pos-word x)         ≅< suc= count-pos-eq >
                sucℕ (count-pos-word y)         ≅<>
                count-pos-word (p1 :: y)        ∎}
        where open WithoutM1 wm1

    neg-to-front : (x : Word) → Either (Σ Word (WithoutM1 x)) (count-neg-word x ≅ℕ 0ℕ)
    neg-to-front [] = right (reflexive-on ℕ 0ℕ)
    neg-to-front (m1 :: x) = left (x , record { 
        without-m1-eq = reflexive-on ℤ (free (m1 :: x));
        count-neg-suc = begin≅
            count-neg-word (m1 :: x)    ≅<>
            sucℕ (count-neg-word x)     ∎;
        count-pos-eq = reflexive-on ℕ (count-pos-word x) })
    neg-to-front (p1 :: x) with neg-to-front x
    ... | left (y , wm1y)   = left (p1 :: y , inc-wm1-p1 wm1y)
    ... | right cnx=0       = right cnx=0

data _≤_ : Rel lzero ℤ where 
    zle : {x y : Word} → x ≤W y → free x ≤ free y

private
    ≤-reflexive : Reflexive _≤_
    ≤-reflexive (free x) = zle (≤W-reflexive x x (refl x x (reflexive-on Word x)))

    ≤-transitive : Transitive _≤_
    ≤-transitive (zle x≤y) (zle y≤z) = zle (≤W-transitive x≤y y≤z)