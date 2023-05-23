open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Map.Properties {ℓA ℓ=A ℓB ℓ=B : Level} (A : Set ℓA) (B : Set ℓB) {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} where

open import Definitions.List
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.List.Setoid {ℓA} {ℓ=A} A renaming ([]=[] to A[]=[]; cons=[]=cons to Acons=cons)
open import Definitions.List.Setoid {ℓB} {ℓ=B} B renaming ([]=[] to B[]=[]; cons=[]=cons to Bcons=cons)
open Setoid {{...}}

map-congruent : (f : A → B) → {{IC : IsCongruent f}} → {a1 a2 : [ A ]} → a1 ≅ a2 → map f a1 ≅ map f a2
map-congruent f A[]=[] = B[]=[]
map-congruent f (Acons=cons a1=a2 as1=as2) = Bcons=cons (congruent-on f a1=a2) (map-congruent f as1=as2)