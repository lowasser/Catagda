{-# OPTIONS --sized-types #-}
module Data.Number.Surreal where

open import Agda.Builtin.Size
open import Data.List

data ∃-element : { A : Set } → [ A ] → (A → Set) → Set where
    this-one : {A : Set} {P : A → Set} → (x : A) → P x → (xs : [ A ]) → ∃-element (x :: xs) P
    another-one : {A : Set} {P : A → Set} → (x : A) → {xs : [ A ]} → ∃-element xs P → ∃-element (x :: xs) P

data ∀-element : {A : Set} → [ A ] → (A → Set) → Set where
    vacuous : {A : Set} {P : A → Set} → ∀-element [] P
    ∀-cons : {A : Set} {P : A → Set} → (x : A) → P x → {xs : [ A ]} → ∀-element xs P → ∀-element (x :: xs) P

interleaved mutual
    data Surreal : Set
    data _⊇_ : Surreal → Surreal → Set
    data _⊉_ : Surreal → Surreal → Set

    is-a-number : [ Surreal ] → [ Surreal ] → Set
    is-a-number l r = ∀-element l (λ xl → ∀-element r (xl ⊉_))

    data Surreal where
        <_∥_>_ : (l r : [ Surreal ]) → is-a-number l r → Surreal

    data _⊇_ where
        geq : {al ar bl br : [ Surreal ]} → {pa : is-a-number al ar} {pb : is-a-number bl br} →
            ∀-element ar ((< bl ∥ br > pb) ⊉_) →
            ∀-element bl (_⊉ (< al ∥ ar > pa)) →
            (< al ∥ ar > pa) ⊇ (< bl ∥ br > pb)

    data _⊉_ where
        ngeql : {al ar bl br : [ Surreal ]} → {ap : is-a-number al ar} {bp : is-a-number bl br} →
            ∃-element ar ((< bl ∥ br > bp) ⊇_) →
            (< al ∥ ar > ap) ⊉ (< bl ∥ br > bp)
        ngeqr : {al ar bl br : [ Surreal ]} → {ap : is-a-number al ar} {bp : is-a-number bl br} →
            ∃-element bl (_⊇ (< al ∥ ar > ap)) →
            (< al ∥ ar > ap) ⊉ (< bl ∥ br > bp)