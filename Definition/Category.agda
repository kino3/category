module Definition.Category where
open import Level public
open import Relation.Binary using (Setoid) public

_[_,_] : ∀ {a b c} {X : Set a} 
  → (h : X → X → Setoid b c) → X → X → Set b
h [ x , y ] = Setoid.Carrier (h x y)

record RawCategory (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    Obj : Set l1
    Hom : Obj → Obj → Setoid l2 l3
    _o_ : {a b c : Obj} → Hom [ b , c ] → Hom [ a , b ] → Hom [ a , c ]
    Id  : (a : Obj) → Hom [ a , a ]

  -- for convenience  
  _≈_ : {a b : Obj} → Hom [ a , b ] → Hom [ a , b ] → Set l3
  _≈_ {a} {b} p q = Setoid._≈_ (Hom a b) p q

record IsCategory {l1 l2 l3 : Level} (rC : RawCategory l1 l2 l3) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  private 
   module C = RawCategory rC
   Obj = C.Obj
   Hom = C.Hom
   _o_ = C._o_
   id  = C.Id
   _≈_ = C._≈_
   
  field
    assoc   : {a b c d : Obj} {f : Hom [ a , b ]} 
              {g : Hom [ b , c ]} {k : Hom [ c , d ]}
            → (k o (g o f)) ≈ ((k o g) o f)
    unitL   : {a b : Obj} {f : Hom [ a , b ]} → (id b o f) ≈ f
    unitR   : {b c : Obj} {g : Hom [ b , c ]} → (g o id b) ≈ g

record Category (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    definition : RawCategory l1 l2 l3
    axioms     : IsCategory definition

  -- for convenience
  private
    module C = RawCategory definition
  Obj = C.Obj 
  Hom = C.Hom 
  _o_ = C._o_ 
  _≈_ = C._≈_
  id  = C.Id
