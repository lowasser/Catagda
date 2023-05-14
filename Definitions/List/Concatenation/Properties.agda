open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Concatenation.Properties {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Definitions.List renaming (_++_ to _+?+_)
open import Definitions.List.Setoid {ℓA} {ℓ=A} (A)
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties 
open import Definitions.Relation.Properties
open import Definitions.List.Properties {ℓA} {ℓ=A} (A)
open import Definitions.Setoid.Equation
open import Definitions.Setoid
open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Semigroup
open import Definitions.Monoid

open Setoid {{...}}
open Equivalence {{...}}
open PreOrder {{...}}
open IsReflexive {{...}}
open IsSymmetric {{...}}
open BiCongruent {{...}}

private
    _++_ : BinOp [ A ]
    _++_ = _+?+_
    
    _:A:_ : A → [ A ] → [ A ]
    _:A:_ = _::_

    ++-left-congruent : LeftCongruent _++_
    ++-left-congruent {[]} ys≅zs = ys≅zs
    ++-left-congruent {x :: xs} {ys} {zs} ys≅zs = begin≅
        (x :: xs) ++ ys     ≅<>
        x :: (xs ++ ys)     ≅< left-congruent (++-left-congruent ys≅zs) >
        x :: (xs ++ zs)     ≅<>
        (x :: xs) ++ zs     ∎

    ++-left-id : LeftIdentity _++_ []
    ++-left-id = reflexive-on [ A ]

    ++-right-id : RightIdentity _++_ []
    ++-right-id nil = nil=[]=nil
    ++-right-id (x :: xs) = begin≅
        (x :: xs) ++ nil    ≅<>
        x :: (xs ++ nil)    ≅< left-congruent-on _::_ (++-right-id xs) >
        x :: xs             ∎
    
    ++-right-congruent : RightCongruent _++_
    ++-right-congruent {[]} {xs} {ys} xs≅ys = begin≅
        xs ++ []        ≅< ++-right-id xs >
        xs              ≅< xs≅ys >
        ys              ≅< symmetric-on [ A ] (++-right-id ys) >
        ys ++ []        ∎
    ++-right-congruent {zs} nil=[]=nil = reflexive-on [ A ] zs
    ++-right-congruent {zs} (cons=[]=cons x≅y xs≅ys) =
        cons=[]=cons (x≅y) (++-right-congruent {zs} xs≅ys)

    ++-left-injective : (xs : [ A ]) → Injective (xs ++_)
    ++-left-injective [] ys≅zs = ys≅zs
    ++-left-injective (x :: xs) (cons=[]=cons _ xsys≅xszs) = ++-left-injective xs xsys≅xszs

instance
    ++-BiCongruent : BiCongruent _++_
    ++-BiCongruent = record {left-congruent = ++-left-congruent; right-congruent = ++-right-congruent}
    
    ++-Magma : Magma _++_
    ++-Magma = make-magma _++_ ++-left-congruent ++-right-congruent

instance
    ++-HasIdentity : HasIdentity _++_ []
    ++-HasIdentity = record { left-identity = ++-left-id ; right-identity = ++-right-id }

private
    ++-assoc : Associate _++_
    ++-assoc [] ys zs = begin≅
        [] ++ (ys ++ zs)    ≅<>
        ys ++ zs            ≅< right-congruent-on _++_ (left-id-on _++_ ys) >
        ([] ++ ys) ++ zs    ∎
    ++-assoc (x :: xs) ys zs = begin≅
        (x :: xs) ++ (ys ++ zs)     ≅<>
        x :: (xs ++ (ys ++ zs))     ≅< left-congruent-on _::_ (++-assoc xs ys zs) >
        x :: ((xs ++ ys) ++ zs)     ≅<>
        (x :: (xs ++ ys)) ++ zs     ≅<>
        ((x :: xs) ++ ys) ++ zs     ∎

instance
    ++-IsAssociative : IsAssociative _++_
    ++-IsAssociative = record { associate = ++-assoc }

    ++-Semigroup : Semigroup _++_
    ++-Semigroup = record {}

    ++-Monoid : Monoid _++_ []
    ++-Monoid = record {}

map-distributes-over-++ : {ℓB : Level} {B : Set ℓB} → (f : B → A) → (xs ys : [ B ]) → map f (xs +?+ ys) ≅ map f xs ++ map f ys
map-distributes-over-++ f [] ys = reflexive-on [ A ] (map f ys)
map-distributes-over-++ f (x :: xs) ys = begin≅
    map f ((x :: xs) +?+ ys)        ≅<>
    map f (x :: (xs +?+ ys))        ≅<>
    f x :: map f (xs +?+ ys)        ≅< left-congruent-on _::_ (map-distributes-over-++ f xs ys) >
    f x :: (map f xs ++ map f ys)   ≅<>
    (f x :: map f xs) ++ map f ys   ≅<>
    map f (x :: xs) ++ map f ys     ∎