open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Semigroup.Free {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} where

open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Relation
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Properties
open import Definitions.List
open import Definitions.List.Setoid (A)
open import Definitions.List.Properties (A)
open import Definitions.List.Concatenation.Properties (A)
open import Definitions.Semigroup
open import Definitions.Setoid.Equation

open Setoid {{...}}

data FreeSemigroup : Set ℓ → Set ℓ where
    free-semi : A → [ A ] → FreeSemigroup A

free-semi1 : A → FreeSemigroup A
free-semi1 x = free-semi x []

data _=fsg=_ : Relation (FreeSemigroup A) where
    =fsg : {x y : A} → x ≅ y → {xs ys : [ A ]} → xs ≅ ys → free-semi x xs =fsg= free-semi y ys

private
    =fsg-reflexive : Reflexive _=fsg=_
    =fsg-reflexive (free-semi x xs) = =fsg (reflexive-on A x) (reflexive-on [ A ] xs)

    =fsg-symmetric : Symmetric _=fsg=_
    =fsg-symmetric (=fsg x≅y xs≅ys) = =fsg (symmetric-on A x≅y) (symmetric-on [ A ] xs≅ys)

    =fsg-transitive : Transitive _=fsg=_
    =fsg-transitive (=fsg x≅y xs≅ys) (=fsg y≅z ys≅zs) = =fsg (transitive-on A x≅y y≅z) (transitive-on [ A ] xs≅ys ys≅zs)

instance
    =fsg-IsReflexive : IsReflexive _=fsg=_
    =fsg-IsReflexive = record {reflexive = =fsg-reflexive}

    =fsg-IsSymmetric : IsSymmetric _=fsg=_
    =fsg-IsSymmetric = record {symmetric = =fsg-symmetric}

    =fsg-IsTransitive : IsTransitive _=fsg=_ 
    =fsg-IsTransitive = record {transitive = =fsg-transitive}

    =fsg-IsEquivalence : Equivalence _=fsg=_
    =fsg-IsEquivalence = record {}

    fsg-Setoid : Setoid (FreeSemigroup A)
    fsg-Setoid = record { _≅_ = _=fsg=_ }

_<sg>_ : BinOp (FreeSemigroup A)
free-semi x xs <sg> free-semi y ys = free-semi x (xs ++ (y :: ys))

private
    sg-bicongruent : BiCongruent _<sg>_
    sg-bicongruent {free-semi x xs} {free-semi y ys} {free-semi z zs} {free-semi w ws} (=fsg x≅y xs≅ys) (=fsg z≅w zs≅ws) =
        =fsg x≅y (begin≅
            xs ++ (z :: zs)     ≅< cong2-on _++_ xs≅ys (cong2-on _::_ z≅w zs≅ws) >
            ys ++ (w :: ws)     ∎)

    free-semi-bicongruent : BiCongruent free-semi
    free-semi-bicongruent x≅y = =fsg x≅y

instance
    sg-IsBiCongruent : IsBiCongruent _<sg>_
    sg-IsBiCongruent = record { cong2 = sg-bicongruent }

    sg-Magma : Magma _<sg>_
    sg-Magma = record {}

    free-semi-IsBiCongruent : IsBiCongruent free-semi
    free-semi-IsBiCongruent = record { cong2 = free-semi-bicongruent }

private
    sg-associate : Associate _<sg>_
    sg-associate (free-semi x xs) (free-semi y ys) (free-semi z zs) = begin≅
        free-semi x (xs ++ (y :: (ys ++ (z :: zs))))    ≅<>
        free-semi x (xs ++ ((y :: ys) ++ (z :: zs)))    ≅< cong-left-on free-semi (left-associate-on _++_ xs (y :: ys) (z :: zs)) >
        free-semi x ((xs ++ (y :: ys)) ++ (z :: zs))    ∎

instance
    sg-IsAssociative : IsAssociative _<sg>_
    sg-IsAssociative = record {associate = sg-associate}

    sg-Semigroup : Semigroup _<sg>_
    sg-Semigroup = record {}