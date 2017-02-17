module Definition.Properties where

open import Definition.Category
open import NotationUtil
open import Data.Product using (Σ-syntax;_×_)

inverses :
  {l1 l2 l3 : Level} 
  {C : Category l1 l2 l3}
  {a b : Obj[ C ]} → C [ a , b ] → Set l2
inverses {l1} {l2} {l3} {C} {a} {b} hom = C [ b , a ]

syntax inverses hom = hom ⁻¹

invertible :
  {l1 l2 l3 : Level} 
  {C : Category l1 l2 l3}
  {a b : Obj[ C ]} → C [ a , b ] → Set (l2 ⊔ l3)
invertible {l1} {l2} {l3} {C} {a} {b} e =
   Σ[ e' ∈ C [ b , a ] ] (C [ (C [ e' ∘ e ]) ≈ C [1 a ] ] × C [ (C [ e ∘ e' ]) ≈ C [1 b ] ])
