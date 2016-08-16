module Definition.Functor where
open import Level
open import Definition.Category

record Functor 
  {l1 l2 l3 m1 m2 m3 : Level} 
  (C : Category l1 l2 l3) 
  (B : Category m1 m2 m3)
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module C = Category C
    module B = Category B
  _≈_ = B._≈_

  field
    Obj-func : C.Obj → B.Obj
    Arrow-func : {c c' : C.Obj} →
               C [ c , c' ] → B [ Obj-func c , Obj-func c' ]

  --syntax sugar
  fo = Obj-func
  fa = Arrow-func

  private
    _∘ᵇ_ = B._o_
    _∘ᶜ_ = C._o_
   
  field
    id   : {c : C.Obj} → fa (C.Id c) ≈ B.Id (fo c)
    comp : {a b c : C.Obj} {f : C [ a , b ]} {g : C [ b , c ]}
           → fa (g ∘ᶜ f) ≈ (fa g ∘ᵇ fa f)

syntax Functor C B = C ⟶ B
