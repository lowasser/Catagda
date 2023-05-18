module Definitions.Int.Ordering where

open import Definitions.Int.Base
open import Definitions.Int.Addition
open import Definitions.Nat renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_; suc to sucℕ)
open import Definitions.Pair
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Definitions.List.Setoid {lzero} {lzero} ⊤
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
open import Definitions.Relation.Properties

private
    Letter Word : Set
    Letter = Either ⊤ ⊤
    Word = [ Letter ]

    _≅ℕ_ : {{SN : Setoid lzero ℕ}} → Rel lzero ℕ
    _≅ℕ_ {{SN}} = _≅_
        where open Setoid SN

    count-pos-word count-neg-word : Word → ℕ
    count-pos-word [] = 0ℕ
    count-pos-word (p1 :: x) = sucℕ (count-pos-word x)
    count-pos-word (m1 :: x) = count-pos-word x

    count-neg-word [] = 0ℕ
    count-neg-word (p1 :: x) = count-neg-word x
    count-neg-word (m1 :: x) = sucℕ (count-neg-word x)

    count-pos count-neg : ℤ → ℕ
    count-pos (free x) = count-pos-word x
    count-neg (free x) = count-neg-word x

    ℕ-to-word : ℕ → Word
    ℕ-to-word 0ℕ = []
    ℕ-to-word (sucℕ n) = p1 :: ℕ-to-word n

    ℕ-to-ℤ : ℕ → ℤ
    ℕ-to-ℤ n = free (ℕ-to-word n)

    open Setoid {{...}}
    open Group {{...}}

    _-ℕ_ : ℕ → ℕ → ℤ
    m -ℕ n = ℕ-to-ℤ m + neg (ℕ-to-ℤ n)

    count-invariant : (x : ℤ) → x ≅ ℕ-to-ℤ (count-pos x) + neg (ℕ-to-ℤ (count-neg x))
    count-invariant (free []) = reflexive-on ℤ 0ℤ
    count-invariant (free (p1 :: x)) = begin≅
        free (p1 :: x)              ≅<>
        1ℤ + free x                 ≅< left-congruent-on _+_ (count-invariant (free x)) >
        1ℤ + (ℕ-to-ℤ (count-pos (free x)) + neg (ℕ-to-ℤ (count-neg (free x))))
                                    ≅< associate-on _+_ 1ℤ (ℕ-to-ℤ (count-pos (free x))) (neg (ℕ-to-ℤ (count-neg (free x)))) >
        (1ℤ + ℕ-to-ℤ (count-pos (free x))) + neg (ℕ-to-ℤ (count-neg (free x)))
                                    ≅<>
        ℕ-to-ℤ (count-pos (free (p1 :: x))) + neg (ℕ-to-ℤ (count-neg (free (p1 :: x))))
                                    ∎
    count-invariant (free (m1 :: x)) = begin≅
        free (m1 :: x)              ≅<>
        -1ℤ + free x                ≅< left-congruent-on _+_ (count-invariant (free x)) >
        -1ℤ + (ℕ-to-ℤ (count-pos (free x)) + neg (ℕ-to-ℤ (count-neg (free x))))
                                    ≅< commute-on _+_ -1ℤ (ℕ-to-ℤ (count-pos (free x)) + neg (ℕ-to-ℤ (count-neg (free x)))) >
        (ℕ-to-ℤ (count-pos (free x)) + neg (ℕ-to-ℤ (count-neg (free x)))) + -1ℤ
                                    ≅< symmetric-on ℤ (associate-on _+_ (ℕ-to-ℤ (count-pos (free x))) (neg (ℕ-to-ℤ (count-neg (free x)))) -1ℤ) >
        ℕ-to-ℤ (count-pos (free x)) + (neg (ℕ-to-ℤ (count-neg (free x))) + neg 1ℤ)
                                    ≅< left-congruent-on _+_ (symmetric-on ℤ (distribute-inverse-on _+_ 0ℤ neg 1ℤ (ℕ-to-ℤ (count-neg (free x))))) >
        ℕ-to-ℤ (count-pos (free x)) + neg (1ℤ + ℕ-to-ℤ (count-neg (free x)))
                                    ≅<>
        ℕ-to-ℤ (count-pos (free (m1 :: x))) + neg (ℕ-to-ℤ (count-neg (free (m1 :: x))))
                                    ∎

    reduce-minus : (a b : ℕ) → (sucℕ a -ℕ sucℕ b) ≅ (a -ℕ b)
    reduce-minus a b = begin≅
        ℕ-to-ℤ (sucℕ a) + neg (ℕ-to-ℤ (sucℕ b))         ≅<>
        (1ℤ + ℕ-to-ℤ a) + neg (1ℤ + ℕ-to-ℤ b)           ≅< left-congruent-on _+_ (distribute-inverse-on _+_ 0ℤ neg 1ℤ (ℕ-to-ℤ b)) >
        (1ℤ + ℕ-to-ℤ a) + (neg (ℕ-to-ℤ b) + neg 1ℤ)     ≅< bi-congruent _+_ (commute-on _+_ 1ℤ (ℕ-to-ℤ a)) (commute-on _+_ (neg (ℕ-to-ℤ b)) (neg 1ℤ)) >
        (ℕ-to-ℤ a + 1ℤ) + (neg 1ℤ + neg (ℕ-to-ℤ b))     ≅< associate-on _+_ (ℕ-to-ℤ a + 1ℤ) (neg 1ℤ) (neg (ℕ-to-ℤ b)) >
        ((ℕ-to-ℤ a + 1ℤ) + neg 1ℤ) + neg (ℕ-to-ℤ b)     ≅< right-congruent-on _+_ (symmetric-on ℤ (associate-on _+_ (ℕ-to-ℤ a) 1ℤ (neg 1ℤ))) >
        (ℕ-to-ℤ a + (1ℤ + neg 1ℤ)) + neg (ℕ-to-ℤ b)     ≅< right-congruent-on _+_ {neg (ℕ-to-ℤ b)} (left-congruent-on _+_ (right-inverse-on _+_ 0ℤ neg 1ℤ)) >
        (ℕ-to-ℤ a + 0ℤ) + neg (ℕ-to-ℤ b)                ≅< right-congruent-on _+_ (right-identity-on _+_ (ℕ-to-ℤ a)) >
        ℕ-to-ℤ a + neg (ℕ-to-ℤ b)                       ∎

    data Δ0 : Set where
        [1+_] : ℕ → Δ0
        -[1+_] : ℕ → Δ0
        Δ=0 : Δ0
    
    Δ0-to-ℤ : Δ0 → ℤ
    Δ0-to-ℤ [1+ n ] = ℕ-to-ℤ (sucℕ n)
    Δ0-to-ℤ -[1+ n ] = neg (ℕ-to-ℤ (sucℕ n))
    Δ0-to-ℤ Δ=0 = 0ℤ

    Canonicalization : (x : ℤ) → Set
    Canonicalization x = Σ Δ0 (λ d → x ≅ Δ0-to-ℤ d)

    canonicalize-helper : (x : Word) → (p n : ℕ) → (free x ≅ p -ℕ n) → Canonicalization (free x)
    canonicalize-helper x (sucℕ p) (sucℕ n) x=sp+nsn = canonicalize-helper x p n (begin≅
        free x              ≅< x=sp+nsn >
        sucℕ p -ℕ sucℕ n   ≅< reduce-minus p n >
        p -ℕ n              ∎)
    canonicalize-helper _ 0ℕ 0ℕ x=0+0 = Δ=0 , x=0+0
    canonicalize-helper _ 0ℕ (sucℕ n) x=0+nsn = -[1+ n ] , x=0+nsn
    canonicalize-helper x (sucℕ p) 0ℕ x=sp-0 = [1+ p ] , (begin≅
        free x                               ≅< x=sp-0 >
        sucℕ p -ℕ 0ℕ                        ≅<>
        ℕ-to-ℤ (sucℕ p) + neg (ℕ-to-ℤ 0ℕ)   ≅<>
        ℕ-to-ℤ (sucℕ p) + 0ℤ                ≅< right-identity-on _+_ (ℕ-to-ℤ (sucℕ p)) >
        ℕ-to-ℤ (sucℕ p)                     ≅<>
        Δ0-to-ℤ [1+ p ]                     ∎)

    canonicalize-word : (x : Word) → Canonicalization (free x)
    canonicalize-word x = canonicalize-helper x (count-pos-word x) (count-neg-word x) (count-invariant (free x))

    canonicalize : (x : ℤ) → Canonicalization x
    canonicalize (free x) = canonicalize-word x
    
    data _Δ0-eq_ : Rel lzero Δ0 where
        1+eq : (m n : ℕ) → m ≅ℕ n → [1+ m ] Δ0-eq [1+ n ]
        -1-eq : (m n : ℕ) → m ≅ℕ n → -[1+ m ] Δ0-eq -[1+ n ]
        Δ=0-eq : Δ=0 Δ0-eq Δ=0

    Δ0-eq-reflexive : Reflexive _Δ0-eq_
    Δ0-eq-reflexive [1+ n ] = 1+eq n n (reflexive-on ℕ n)
    Δ0-eq-reflexive -[1+ n ] = -1-eq n n (reflexive-on ℕ n)
    Δ0-eq-reflexive Δ=0 = Δ=0-eq

    Δ0-eq-symmetric : Symmetric _Δ0-eq_
    Δ0-eq-symmetric (1+eq m n m=n) = 1+eq n m (symmetric-on ℕ m=n)
    Δ0-eq-symmetric (-1-eq m n m=n) = -1-eq n m (symmetric-on ℕ m=n)
    Δ0-eq-symmetric Δ=0-eq = Δ=0-eq

    Δ0-eq-transitive : Transitive _Δ0-eq_
    Δ0-eq-transitive (1+eq a b a=b) (1+eq b c b=c) = 1+eq a c (transitive-on ℕ a=b b=c)
    Δ0-eq-transitive (-1-eq a b a=b) (-1-eq b c b=c) = -1-eq a c (transitive-on ℕ a=b b=c)
    Δ0-eq-transitive Δ=0-eq Δ=0-eq = Δ=0-eq

    instance
        Δ0-eq-is-reflexive : IsReflexive _Δ0-eq_
        Δ0-eq-is-reflexive = record {reflexive = Δ0-eq-reflexive}

        Δ0-eq-is-symmetric : IsSymmetric _Δ0-eq_
        Δ0-eq-is-symmetric = record {symmetric = Δ0-eq-symmetric}

        Δ0-eq-is-transitive : IsTransitive _Δ0-eq_
        Δ0-eq-is-transitive = record {transitive = Δ0-eq-transitive}

        Δ0-eq-preorder : PreOrder _Δ0-eq_
        Δ0-eq-preorder = record {}

        Δ0-equivalence : Equivalence _Δ0-eq_
        Δ0-equivalence = record {}

        Δ0-setoid : Setoid lzero Δ0
        Δ0-setoid = record { _≅_ = _Δ0-eq_ }

    canonicalization-unique-word : (x y : Word) → EqClosure x y → fst (canonicalize-word x) Δ0-eq fst (canonicalize-word y)
    canonicalization-unique-word x y (imp x₁) = {!   !}
    canonicalization-unique-word 0ℕ 0ℕ (refl 0ℕ 0ℕ nil=[]=nil) = Δ=0-eq
    canonicalization-unique-word (p1 :: x) (p1 :: y) (refl (p1 :: x) (p1 :: y) (cons=[]=cons (r= _) x=y)) = {!   !}
    canonicalization-unique-word x y (sym y=x) = symmetric-on Δ0 (canonicalization-unique-word y x y=x)
    canonicalization-unique-word x y (trans {x} {z} {y} x=z z=y) = transitive-on Δ0 (canonicalization-unique-word x z x=z) (canonicalization-unique-word z y z=y)