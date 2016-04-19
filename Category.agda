module Category where
open import Level
open import Relation.Binary using (Setoid)


_[_,_] : ∀ {a b c} {X : Set a} 
  → (h : X → X → Setoid b c) → X → X → Set b
h [ x , y ] = Setoid.Carrier (h x y)

record RawCategory (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    Obj : Set l1
    Hom : Obj → Obj → Setoid l2 l3
    _o_ : {a b c : Obj} → Hom [ b , c ] → Hom [ a , b ] → Hom [ a , c ]
    Id  : (a : Obj) → Hom [ a , a ]

{-
record isCategory {l1 l2 l3 : Level} (rC : RawCategory l1 l2 l3) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  private 
   module C = RawCategory rC
   _o_ = C._o_
   _≈_ = C.
  field
    assoc   : {a b c d : C.Obj} {f : C.Hom [ a , b ]} {g : C.Hom [ b , c ]} {k : C.Hom [ c , d ]}
            → k o (g o f) ≈ (k o g) o f
    unitL   : {a b : Obj} {f : Hom a b} → id b o f ≈ f
    unitR   : {b c : Obj} {g : Hom b c} → g o id b ≈ g
-}



record Category (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    definition : RawCategory l1 l2 l3
    --axioms     : isCategory definition
