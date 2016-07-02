module Definition.NaturalTransformation where

open import Level
open import Definition.Category
open import Definition.Functor

record RawNaturalTransformation
  {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  (S T : Functor C B) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module C = Category C
    module B = Category B
    module S = Functor S
    module T = Functor T

  field
    τ : (c : C.Obj) → B.Hom [ S.o c , T.o c ]

record IsNaturalTransformation
  {l1 l2 l3 m1 m2 m3 : Level}
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  {S T : Functor C B}
  (rN : RawNaturalTransformation S T)
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module S = Functor S
    module T = Functor T
    module B = Category B
    module C = Category C
    τ = RawNaturalTransformation.τ rN
    _≈_ = B._≈_
    _∘_ = B._o_
   
  field
    commute : {c c' : C.Obj} {f : C.Hom [ c , c' ]}
            → (τ c' ∘ S.a f) ≈ (T.a f ∘ τ c)

record _∸>_  (l1 l2 l3 m1 m2 m3 : Level)
  {l1 l2 l3 m1 m2 m3 : Level}
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  (S T : Functor C B)
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where
  field
    definition : RawNaturalTransformation S T 
    axioms     : IsNaturalTransformation definition


