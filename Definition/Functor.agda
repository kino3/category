module Definition.Functor where
open import Level
open import Definition.Category
open import Data.String

record RawFunctor 
  {l1 l2 l3 m1 m2 m3 : Level} 
  (C : Category l1 l2 l3) 
  (B : Category m1 m2 m3) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module C = Category C
    module B = Category B
  _≈_ = B._≈_

  field
    Obj-func : C.Obj → B.Obj
    Arrow-func : {c c' : C.Obj} →
               C.Hom [ c , c' ] → B.Hom [ Obj-func c , Obj-func c' ]

  --syntax sugar
  o = Obj-func
  a = Arrow-func

record IsFunctor 
  {l1 l2 l3 m1 m2 m3 : Level}
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  (rF : RawFunctor C B) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module T = RawFunctor rF
    module B = Category B
    module C = Category C
    _≈_ = B._≈_
    _∘ᵇ_ = B._o_
    _∘ᶜ_ = C._o_
   
  field
    id   : {c : C.Obj} → T.a (C.id c) ≈ B.id (T.o c)
    comp : {a b c : C.Obj} {f : C.Hom [ a , b ]} {g : C.Hom [ b , c ]}
           → T.a (g ∘ᶜ f) ≈ (T.a g ∘ᵇ T.a f)

record Functor (l1 l2 l3 m1 m2 m3 : Level)
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where
  field
    definition : RawFunctor C B 
    axioms     : IsFunctor definition
