module Definition.NaturalTransformation where

open import Level
open import Definition.Category
open import Definition.Functor
open import NotationUtil

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
    τ : (c : C.Obj) → B [ S.fo c , T.fo c ]

  _∘_ = B._o_
   
  field
    commute : {c c' : C.Obj} {f : C [ c , c' ]}
            → B [ (τ c' ∘ S.fa f) ≈ (T.fa f ∘ τ c) ]

syntax NaturalTransformation S T = S ∸> T

components-of : {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  {S T : Functor C B} {c : Obj[ C ]} → S ∸> T → Set m2
components-of {l1} {l2} {l3} {m1} {m2} {m3} {C} {B} {S} {T} {c} τ = B [ S.fo c , T.fo c ]
  where
    module S = Functor S
    module T = Functor T

component : {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  {S T : Functor C B} → S ∸> T → (c : Obj[ C ]) → B [ Functor.fo S c , Functor.fo T c ]
component {l1} {l2} {l3} {m1} {m2} {m3} {C} {B} {S} {T} τ c = NaturalTransformation.τ τ c

inverses :
  {l1 l2 l3 : Level} 
  {C : Category l1 l2 l3}
  {a b : Obj[ C ]} → C [ a , b ] → Set l2
inverses {l1} {l2} {l3} {C} {a} {b} hom = C [ b , a ]

syntax inverses hom = hom ⁻¹

-- TODO: invertible?

open import Data.Product

natural-equivalence :
  {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3}
  (S T : Functor C B) → Set {!!} 
natural-equivalence {l1} {l2} {l3} {m1} {m2} {m3} {C} {B} S T
  =  {!!} --Σ[ τ ∈ S ∸> T ] (∀ (c : Obj[ C ]) → {!!})
