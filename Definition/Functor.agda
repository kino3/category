module Definition.Functor where
open import Level
open import Definition.Category
open import NotationUtil

record Functor 
  {l1 l2 l3 m1 m2 m3 : Level} 
  (C : Category l1 l2 l3) 
  (B : Category m1 m2 m3)
  : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  private
    module C = Category C
    module B = Category B

  field
    fo : C.Obj → B.Obj
    fa : {c c' : C.Obj} →
               C [ c , c' ] → B [ fo c , fo c' ]

  private
    _∘ᵇ_ = B._o_
    _∘ᶜ_ = C._o_
  field
    id   : {c : C.Obj} → B [ fa (C [1 c ]) ≈ B [1 (fo c) ] ]
    comp : {a b c : C.Obj} {f : C [ a , b ]} {g : C [ b , c ]}
           → B [ fa (g ∘ᶜ f) ≈ (fa g ∘ᵇ fa f) ]
    ≈-resp : {a b : C.Obj} (f g : C [ a , b ]) 
           → C [ f ≈ g ] → B [ fa f ≈ fa g ]

syntax Functor C B = C ⟶ B

{-
FunctorSetoid :
  {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3}
  {B : Category m1 m2 m3} → 
  Functor C B → Setoid {!!} {!!}
FunctorSetoid {l1} {l2} {l3} {m1} {m2} {m3} {C} {B} f = record {
                    Carrier = Functor C B;
                    _≈_ = {!!} ;
                    isEquivalence = {!!} }
-}
