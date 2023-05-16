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
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.List 
open import Definitions.Setoid.Equation
open import Definitions.Function.Binary.Properties
open import Definitions.Either
open import Definitions.Group

open Setoid {{...}}
open Group {{...}}

private
    ℕ-to-free : ℕ → [ Either ⊤ ⊤ ]
    ℕ-to-free 0ℕ = []
    ℕ-to-free (sucℕ n) = p1 :: ℕ-to-free n

    record free-count-proof (x : [ Either ⊤ ⊤ ]) : Set where
        field
            plus : ℕ
            minus : ℕ
            pf : free x ≅ free (ℕ-to-free plus) + neg (free (ℕ-to-free minus))

    fcp0 : free-count-proof []
    fcp0 = record {
        plus = 0ℕ;
        minus = 0ℕ;
        pf = reflexive-on ℤ 0ℤ}

    inc-fcp : (i : Either ⊤ ⊤) (x : [ Either ⊤ ⊤ ]) (fcp : free-count-proof x) → free-count-proof (i :: x)
    inc-fcp p1 x fcp = record { 
        plus = sucℕ plus;
        minus = minus;
        pf = begin≅
            free (p1 :: x)          ≅<>
            1ℤ + free x             ≅< left-congruent-on _+_ pf >
            1ℤ + (free (ℕ-to-free plus) + neg (free (ℕ-to-free minus)))
                                    ≅< associate-on _+_ 1ℤ (free (ℕ-to-free plus)) (neg (free (ℕ-to-free minus))) >
            (1ℤ + free (ℕ-to-free plus)) + neg (free (ℕ-to-free minus))
                                    ≅<>
            (free (p1 :: ℕ-to-free plus)) + neg (free (ℕ-to-free minus))
                                    ≅<>
            free (ℕ-to-free (sucℕ plus)) + neg (free (ℕ-to-free minus)) ∎}
        where   plus = free-count-proof.plus fcp
                minus = free-count-proof.minus fcp
                pf = free-count-proof.pf fcp
    inc-fcp m1 x fcp = record { 
        plus = plus;
        minus = sucℕ minus;
        pf = begin≅
            free (m1 :: x)          ≅<>
            -1ℤ + free x            ≅< left-congruent-on _+_ pf >
            -1ℤ + (free (ℕ-to-free plus) + neg (free (ℕ-to-free minus)))
                                    ≅< commute-on _+_ -1ℤ (free (ℕ-to-free plus) + neg (free (ℕ-to-free minus))) >
            (free (ℕ-to-free plus) + neg (free (ℕ-to-free minus))) + -1ℤ
                                    ≅< symmetric-on ℤ (associate-on _+_ (free (ℕ-to-free plus)) (neg (free (ℕ-to-free minus))) -1ℤ) >
            free (ℕ-to-free plus) + (neg (free (ℕ-to-free minus)) + -1ℤ)
                                    ≅< left-congruent-on _+_ (symmetric-on ℤ (distribute-inverse 1ℤ (free (ℕ-to-free minus)))) >
            free (ℕ-to-free plus) + neg (1ℤ + free (ℕ-to-free minus))
                                    ≅<>
            free (ℕ-to-free plus) + neg (free (p1 :: ℕ-to-free minus))
                                    ≅<>
            free (ℕ-to-free plus) + neg (free (ℕ-to-free (sucℕ minus)))
                                    ∎}
        where   plus = free-count-proof.plus fcp
                minus = free-count-proof.minus fcp
                pf = free-count-proof.pf fcp

    data zfcp : ℤ → Set where
        zfcp-c : (x : [ Either ⊤ ⊤ ]) → free-count-proof x → zfcp (free x)

    make-zfcp : (x : ℤ) → zfcp x
    make-zfcp (free []) = zfcp-c [] fcp0
    make-zfcp (free (e :: x)) with make-zfcp (free x)
    ... | zfcp-c x fcp-x = zfcp-c (e :: x) (inc-fcp e x fcp-x)

    