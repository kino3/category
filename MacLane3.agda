module MacLane3 where

open import MacLane1
open import Data.Product using (∃!)

-- 1. Universal Arrows
record universal-arrow-from_to_ 
  {l1 l2 l3 m1 m2 m3 : Level} {C : Category l1 l2 l3} {D : Category m1 m2 m3} 
  (c : Category.Obj C) (S : Functor D C) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where
  
  field
    r : Category.Obj D
    u : C [ c , Functor.Tₒ S r ]
    -- such that 
    property : {d : Category.Obj D} {f : C [ c , Functor.Tₒ S d ]} 
      → ∃! (Category._≈_ D) (λ (f' :  D [ r , d ]) → C [ C [ Functor.Tₕ S f' o u ] ≈ f ])

-- 2. The Yoneda Lemma
open import Function.Bijection
-- Bijection of Hom-sets
_≅_ : {l m : Level} → Set l → Set m → Set (suc (l ⊔ m))
A ≅ B = Bijection (record { Carrier = A ; _≈_ = {!!} ; isEquivalence = {!!} }) 
                  (record { Carrier = B ; _≈_ = {!!} ; isEquivalence = {!!} })

--hoge : Bijective (record { _⟨$⟩_ = {!!} ; cong = {!!} })
--hoge = record { injective = {!!} ; surjective = {!!} }

Proposition1 : 
 {l1 l2 l3 m1 m2 m3 : Level} {C : Category l1 l2 l3} {D : Category m1 m2 m3} 
 {c : Category.Obj C} {S : Functor D C} → 
    universal-arrow-from c to S → {!!}
Proposition1 prf = {!!}
