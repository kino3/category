module MacLane1 where

open import Level

-- definition using hom-set

record Category {l m n : Level} : Set (suc (l ⊔ m ⊔ n)) where
  field
    O : Set n
    Hom : (a b : O) → Set m
    _∘_ : {a b c : O} → Hom b c → Hom a b → Hom a c
    id : (c : O) → Hom c c
  dom : {a b : O} → Hom a b → O
  dom {d} {c} = λ x → d
  cod : {a b : O} → Hom a b → O
  cod {d} {c} = λ x → c

-- use   
--open import Categories.Category

a : {l1 l2 l3 : Level} → Category l1 l2 l3 
a = λ {l1} {l2} {l3} → record { Obj = {!!}; _⇒_ = {!!} }
    

