open import Agda.Primitive
open import Structure.Setoid

module Data.List.Map.Properties {ℓA ℓ=A ℓB ℓ=B : Level} (A : Set ℓA) (B : Set ℓB) {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} where

open import Data.List
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Data.List.Setoid {ℓA} {ℓ=A} A renaming ([]=[] to A[]=[]; cons=[]=cons to Acons=cons)
open import Data.List.Setoid {ℓB} {ℓ=B} B renaming ([]=[] to B[]=[]; cons=[]=cons to Bcons=cons)
open Setoid {{...}}

map-congruent : (f : A → B) → {{IC : IsCongruent f}} → {a1 a2 : [ A ]} → a1 ≅ a2 → map f a1 ≅ map f a2
map-congruent f A[]=[] = B[]=[]
map-congruent f (Acons=cons a1=a2 as1=as2) = Bcons=cons (congruent-on f a1=a2) (map-congruent f as1=as2)