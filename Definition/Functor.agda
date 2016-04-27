module Definition.Functor where
open import Level
open import Definition.Category

record Functor 
  {l1 l2 l3 m1 m2 m3 : Level} 
  (C : Category l1 l2 l3) 
  (B : Category m1 m2 m3) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module C = Category C
    module B = Category B

  field
    Obj-func : C.Obj → B.Obj
    Arrow-func : {c c' : C.Obj} → C.Hom [ c , c' ] → B.Hom [ Obj-func c , Obj-func c' ]
  
