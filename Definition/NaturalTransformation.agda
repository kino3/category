module Definition.NaturalTransformation where

open import Level
open import Definition.Category
open import Definition.Functor

record NaturalTransformation
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
    τ : (c : C.Obj) → B.Hom [ S.To c , T.To c ]

  _≈_ = B._≈_
  _∘_ = B._o_
   
  field
    commute : {c c' : C.Obj} {f : C.Hom [ c , c' ]}
            → (τ c' ∘ S.Ta f) ≈ (T.Ta f ∘ τ c)

syntax NaturalTransformation S T = S ∸> T
{-
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


-}

