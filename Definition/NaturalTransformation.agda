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
    τ : (c : C.Obj) → B.Hom [ S.fo c , T.fo c ]

  _≈_ = B._≈_
  _∘_ = B._o_
   
  field
    commute : {c c' : C.Obj} {f : C.Hom [ c , c' ]}
            → (τ c' ∘ S.fa f) ≈ (T.fa f ∘ τ c)

syntax NaturalTransformation S T = S ∸> T

open import Relation.Binary.PropositionalEquality using (_≡_)
NaturalTransformation' :
  {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  (S T : Functor C B) → Setoid _ _
NaturalTransformation' {l1} {l2} {l3} {m1} {m2} {m3} {C} {B} S T =
  record { Carrier = NaturalTransformation S T ;
           _≈_ = {!!} ;
           isEquivalence = {!!} }
