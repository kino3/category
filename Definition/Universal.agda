module Definition.Universal where

open import Definition.Category
open import Definition.Functor
open import Data.Product

record universal-arrow-from_to_
  {l1 l2 l3 m1 m2 m3 : Level} 
  {D : Category l1 l2 l3}
  {C : Category m1 m2 m3} 
  (c : Obj[ C ])
  (S : D ⟶ C)
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module S = Functor S
    _≈_ = Category._≈_ D
    _∘_ = Category._o_ C

  field
    r : Obj[ D ]
    u : C [ c , S.fo r ]
    universality : (d : Obj[ D ]) (f : C [ c , S.fo d ])
      → ∃! _≈_ (λ (f' : D [ r , d ]) → C [ ((S.fa f') ∘ u) ≈ f ])
