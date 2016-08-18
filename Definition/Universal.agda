module Definition.Universal where

open import Definition.Category
open import Definition.Functor
open import Data.Product

data Universal {l1 l2 l3 m1 m2 m3 : Level} 
  {D : Category l1 l2 l3}
  {C : Category m1 m2 m3} 
  {c : Obj[ C ]}
  {S : D ⟶ C}
  (r : Obj[ D ])
  (u : C [ c , (Functor.fo S) r ])
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where
  universality :
    (d : Obj[ D ]) →
    (f : C [ c , (Functor.fo S) d ]) → 
    (∃! (Category._≈_ D) ((λ (f' : D [ r , d ]) → C [ C [ Functor.fa S f' ∘ u ] ≈ f ]))) →
      Universal r u

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
    prop : (d : Obj[ D ]) (f : C [ c , S.fo d ])
      → ∃! _≈_ (λ (f' : D [ r , d ]) → C [ ((S.fa f') ∘ u) ≈ f ])

universal-from_to_ : {l1 l2 l3 m1 m2 m3 : Level} 
  {D : Category l1 l2 l3}
  {C : Category m1 m2 m3} 
  (c : Obj[ C ])
  (S : D ⟶ C)
  (r : Obj[ D ])
  (u : C [ c , (Functor.fo S) r ])
  → Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3))
(universal-from c to S) r u = {!!} --universal-arrow-from c to S

{-
_is_ : ∀ {m n} → (Set m) → (Set m → Set n) → Set n
A is p = p A
-}
