module MacLane3 where

open import MacLane1
open import Data.Product using (∃!)

-- 1. Universal Arrows
record universal-arrow-from_to_ 
  {l1 l2 l3 m1 m2 m3 : Level} {C : Category l1 l2 l3} {D : Category m1 m2 m3} 
  (c : Category.Obj C) (S : Functor D C) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where
  constructor <_,_>_
  field
    r : Category.Obj D
    u : C [ c , Functor.Tₒ S r ]
    -- such that 
    property : {d : Category.Obj D} {f : C [ c , Functor.Tₒ S d ]} 
      → ∃! (Category._≈_ D) (λ (f' :  D [ r , d ]) → C [ C [ Functor.Tₕ S f' o u ] ≈ f ])

-- 2. The Yoneda Lemma
open import Function.Bijection

Proposition1 : 
 {l1 l2 l3 m1 m2 m3 : Level} {C : Category l1 l2 l3} {D : Category m1 m2 m3} 
 {c : Category.Obj C} {S : Functor D C} → 
    universal-arrow-from c to S → Bijection ? ?
Proposition1 prf = {!!}

-- representation

-- Proposition 2.

-- Lemma(Yoneda)
--yoneda : 
