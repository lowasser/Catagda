open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Group.Free {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Definitions.Relation.Properties
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.Magma
open import Definitions.Group
open import Definitions.Monoid
open import Definitions.Semigroup
open import Definitions.Either
open import Definitions.List
open import Definitions.List.Reverse
open import Definitions.Relation
open import Definitions.Setoid.Equation

-- Defining operations depend on decidability broke.  Note to self: don't try it again.

private
    Letter : Set ℓA
    Letter = Either A A 

    Word : Set ℓA
    Word = [ Letter ]

    invLetter : Letter → Letter
    invLetter (left a) = right a
    invLetter (right a) = left a

data FreeGroup : Set ℓA → Set ℓA where
    free : Word → FreeGroup A

open import Definitions.List.Reverse.Properties {ℓA} {ℓ=A} Letter
open import Definitions.Either.Setoid {ℓA} {ℓ=A} {ℓA} {ℓ=A} A A
open import Definitions.List.Setoid {ℓA} {ℓ=A} Letter
open import Definitions.List.Concatenation.Properties {ℓA} {ℓ=A} Letter
open import Definitions.List.Properties {ℓA} {ℓ=A} Letter

open Setoid {{...}}
open Monoid {{...}}
open Semigroup {{...}}
open Magma {{...}}
open Equivalence {{...}}
open IsReflexive {{...}}

data ReducesTo : Rel (ℓA ⊔ ℓ=A) Word where
    reduces : (xs : Word) → (x : Letter) → (ys : Word) → ReducesTo (xs ++ invLetter x :: x :: ys) (xs ++ ys)

data EqClosure : Rel (ℓA ⊔ ℓ=A) Word where
    imp : {xs ys : Word} → ReducesTo xs ys → EqClosure xs ys
    refl : (xs ys : Word) → xs ≅ ys → EqClosure xs ys
    sym : Symmetric EqClosure
    trans : Transitive EqClosure

data EqFg : Rel (ℓA ⊔ ℓ=A) (FreeGroup A) where
    eqfg : { xs ys : Word } → EqClosure xs ys → EqFg (free xs) (free ys)

refl' : {xs ys : Word} → xs ≅ ys → EqClosure xs ys
refl' {xs} {ys} xs=ys = refl xs ys xs=ys

private 
    eqfg-refl : Reflexive EqFg
    eqfg-refl (free xs) = eqfg (refl' (reflexive-on Word xs))

    eqfg-sym : Symmetric EqFg
    eqfg-sym (eqfg xs=ys) = eqfg (sym xs=ys)

    eqfg-trans : Transitive EqFg
    eqfg-trans (eqfg xs=ys) (eqfg ys=zs) = eqfg (trans xs=ys ys=zs)

instance
    fg-setoid : Setoid (ℓA ⊔ ℓ=A) (FreeGroup A)
    fg-setoid = make-setoid EqFg eqfg-refl eqfg-trans eqfg-sym

_∙_ : BinOp (FreeGroup A)
free xs ∙ free ys = free (xs ++ ys)

private
    left-cong' : (xs : Word) → {ys zs : Word} → EqClosure ys zs → EqClosure (xs ++ ys) (xs ++ zs)
    left-cong' xs (refl ys zs ys=zs) = refl (xs ++ ys) (xs ++ zs) (left-congruent-on _++_ ys=zs)
    left-cong' xs (sym zs=ys) = sym (left-cong' xs zs=ys)
    left-cong' xs (trans {ys} {ws} {zs} ys=ws ws=zs) = trans (left-cong' xs ys=ws) (left-cong' xs ws=zs)
    left-cong' xs (imp (reduces ys1 y ys2)) = trans 
        (refl 
                (xs ++ ys1 ++ invLetter y :: y :: ys2) 
                ((xs ++ ys1) ++ invLetter y :: y :: ys2) 
                (associate-on _++_ xs ys1 (invLetter y :: y :: ys2)))
        (trans 
            (imp (reduces (xs ++ ys1) y ys2)) 
            (refl
                ((xs ++ ys1) ++ ys2)
                (xs ++ ys1 ++ ys2) 
                (symmetric-on Word (associate-on _++_ xs ys1 ys2))))

    right-cong' : (xs : Word) → {ys zs : Word} → EqClosure ys zs → EqClosure (ys ++ xs) (zs ++ xs)
    right-cong' xs (refl ys zs ys=zs) = refl (ys ++ xs) (zs ++ xs) (right-congruent-on _++_ ys=zs)
    right-cong' xs (sym zs=ys) = sym (right-cong' xs zs=ys)
    right-cong' xs (trans {ys} {ws} {zs} ys=ws ws=zs) = trans (right-cong' xs ys=ws) (right-cong' xs ws=zs)
    right-cong' xs (imp (reduces ys1 y ys2)) = trans 
        (refl' 
            (symmetric-on Word 
                (associate-on _++_ ys1 (invLetter y :: y :: ys2) xs)))
        (trans
            (imp (reduces ys1 y (ys2 ++ xs))) 
            (refl' (associate-on _++_ ys1 ys2 xs)))

    left-cong : LeftCongruent _∙_
    left-cong {free xs} (eqfg ys=zs) = eqfg (left-cong' xs ys=zs)

    right-cong : RightCongruent _∙_
    right-cong {free xs} (eqfg ys=zs) = eqfg (right-cong' xs ys=zs)

instance
    ∙fg-bicongruent : BiCongruent _∙_
    ∙fg-bicongruent = record {left-congruent = left-cong; right-congruent = right-cong}

    ∙fg-magma : Magma _∙_
    ∙fg-magma = record {}

private
    ∙-assoc : Associate _∙_
    ∙-assoc (free xs) (free ys) (free zs) = eqfg (refl' (associate-on _++_ xs ys zs))

instance
    ∙fg-is-associative : IsAssociative _∙_ 
    ∙fg-is-associative = record {associate = ∙-assoc}

    ∙fg-semigroup : Semigroup _∙_
    ∙fg-semigroup = record {}

1fg : FreeGroup A
1fg = free []

private
    ∙-leftid : LeftIdentity _∙_ 1fg
    ∙-leftid (free xs) = eqfg (refl' (left-id-on _++_ xs))

    ∙-rightid : RightIdentity _∙_ 1fg
    ∙-rightid (free xs) = eqfg (refl' (right-id-on _++_ xs))

instance
    ∙-has-inverse : HasIdentity _∙_ 1fg
    ∙-has-inverse = record {left-identity = ∙-leftid; right-identity = ∙-rightid}

    ∙fg-monoid : Monoid _∙_ 1fg
    ∙fg-monoid = record {}

open Monoid {{...}}

inverse : FreeGroup A → FreeGroup A
inverse (free xs) = free (map invLetter (reverse xs))

private
    invLetter-invLetter : (x : Letter) → invLetter (invLetter x) ≅ x
    invLetter-invLetter (left x) = reflexive-on Letter (left x)
    invLetter-invLetter (right x) = reflexive-on Letter (right x)
    
    left-inv : LeftInverse _∙_ 1fg inverse
    left-inv (free []) = reflexive-on (FreeGroup A) 1fg
    left-inv (free (x :: xs)) = begin≅
        free (map invLetter (reverse (x :: xs))) ∙ free (x :: xs)       ≅<>
        free (map invLetter (reverse (x :: xs)) ++ x :: xs)             ≅<>
        free (map invLetter (reverse xs ++ [ x :]) ++ x :: xs)          ≅< eqfg (refl' (right-congruent-on _++_ (map-distributes-over-++ invLetter (reverse xs) [ x :]))) >
        free ((map invLetter (reverse xs) ++ [ invLetter x :]) ++ x :: xs)  ≅< eqfg (refl' (symmetric-on Word (associate-on _++_ (map invLetter (reverse xs)) [ invLetter x :] (x :: xs)))) >
        free (map invLetter (reverse xs) ++ (invLetter x :: x :: xs))       ≅< eqfg (imp (reduces (map invLetter (reverse xs)) x xs)) >
        free (map invLetter (reverse xs) ++ xs)                         ≅<>
        inverse (free xs) ∙ free xs                                     ≅< left-inv (free xs) >
        1fg                                                             ∎ 

    right-inv : RightInverse _∙_ 1fg inverse
    right-inv (free []) = reflexive-on (FreeGroup A) 1fg
    right-inv (free (x :: xs)) = begin≅
        free (x :: xs) ∙ inverse (free (x :: xs))                       ≅<>
        free ((x :: xs) ++ map invLetter (reverse (x :: xs)))           ≅<>
        free (x :: (xs ++ map invLetter (reverse xs ++ [ x :])))        ≅<>
        free ([ x :] ++ (xs ++ map invLetter (reverse xs ++ [ x :])))   ≅<>
        free [ x :] ∙ free (xs ++ map invLetter (reverse xs ++ [ x :])) ≅< left-cong { free [ x :]} (eqfg (refl' (left-congruent-on _++_ (map-distributes-over-++ invLetter (reverse xs) [ x :])))) >
        free [ x :] ∙ free (xs ++ (map invLetter (reverse xs) ++ [ invLetter x :])) 
                                                                        ≅< left-cong { free [ x :]} (eqfg (refl' (associate-on _++_ xs (map invLetter (reverse xs)) [ invLetter x :]))) >
        free [ x :] ∙ free ((xs ++ map invLetter (reverse xs)) ++ [ invLetter x :])
                                                                        ≅<>
        free [ x :] ∙ ((free xs ∙ inverse (free xs)) ∙ free [ invLetter x :])
                                                                        ≅< left-cong { free [ x :]} (right-congruent-on _∙_ (right-inv (free xs))) >
        free [ x :] ∙ (1fg ∙ free [ invLetter x :])                     ≅<>
        free [ x :] ∙ (free [] ∙ free [ invLetter x :])                 ≅<>
        free [ x :] ∙ free ([] ++ [ invLetter x :])                     ≅<>
        free [ x :] ∙ free [ invLetter x :]                             ≅<>
        free (x :: invLetter x :: [])                                   ≅< eqfg (refl' (right-congruent-on _::_ (symmetric-on Letter (invLetter-invLetter x)))) >
        free (invLetter (invLetter x) :: invLetter x :: [])             ≅<>
        free ([] ++ invLetter (invLetter x) :: invLetter x :: [])       ≅< eqfg (imp (reduces [] (invLetter x) [])) >
        free ([] ++ [])                                                 ≅<>
        1fg                                                             ∎

instance
    fg-has-inverse : HasInverse _∙_ 1fg inverse
    fg-has-inverse = record { left-inverse = left-inv; right-inverse = right-inv }

    fg-group : Group _∙_ 1fg inverse
    fg-group = record {}