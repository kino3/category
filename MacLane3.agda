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
_≅_ : {l1 l2 l3 m1 m2 m3 : Level} {C : Category l1 l2 l3} {X : Category m1 m2 m3} 
      {c : Category.Obj C} {x : Category.Obj X}
      {F : Functor X C} {G : Functor C X} 
      → C [ Functor.Tₒ F x , c ] → X [ x , Functor.Tₒ G c ] → Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3))
a ≅ b = {!!} 

--hoge : Bijective (record { _⟨$⟩_ = {!!} ; cong = {!!} })
--hoge = record { injective = {!!} ; surjective = {!!} }

Proposition1 : 
 {l1 l2 l3 m1 m2 m3 : Level} {C : Category l1 l2 l3} {D : Category m1 m2 m3} 
 {c : Category.Obj C} {S : Functor D C} → 
    universal-arrow-from c to S → {!!}
Proposition1 prf = {!!}
