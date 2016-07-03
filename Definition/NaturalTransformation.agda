module Definition.NaturalTransformation where

open import Level
open import Definition.Category
open import Definition.Functor

record RawNaturalTransformation
  {l1 l2 l3 m1 m2 m3 : Level} 
  {C : RawCategory l1 l2 l3} 
  {B : RawCategory m1 m2 m3}
  (S T : RawFunctor C B) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module C = RawCategory C
    module B = RawCategory B
    module S = RawFunctor S
    module T = RawFunctor T

  field
    τ : (c : C.Obj) → B.Hom [ S.o c , T.o c ]

record IsNaturalTransformation
  {l1 l2 l3 m1 m2 m3 : Level}
  {C : RawCategory l1 l2 l3} 
  {B : RawCategory m1 m2 m3}
  {S T : RawFunctor C B}
  (rN : RawNaturalTransformation S T)
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module S = RawFunctor S
    module T = RawFunctor T
    module B = RawCategory B
    module C = RawCategory C
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
    definition : RawNaturalTransformation (Functor.definition S)
                                          (Functor.definition T) 
    axioms     : IsNaturalTransformation definition

  -- for convenience
  τ = RawNaturalTransformation.τ definition
  commute = IsNaturalTransformation.commute axioms


