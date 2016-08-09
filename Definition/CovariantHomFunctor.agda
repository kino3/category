module Definition.CovariantHomFunctor where

open import Definition.Category hiding (_[_,_])
open import Definition.Functor
open import Category.Sets
import Relation.Binary.EqReasoning as EqR

-- FIXME : move to Util.Notation?
Obj[_] : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set l1
Obj[ C ] = Category.Obj C

_[_,_] :
    {l1 l2 l3 : Level}
  → (C : Category l1 l2 l3)
  → Obj[ C ] → Obj[ C ] → Set l2
C [ x , y ] =
  Setoid.Carrier
    (Category.Hom C x y)

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y Z} → (C [ Y , Z ]) → (C [ X , Y ])
       → C [ X , Z ]
_[_∘_] = Category._o_ 

_[_≈_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y} → (f g : C [ X , Y ]) → Set e
_[_≈_] = Category._≈_

_[1_] : ∀ {o ℓ e}
       → (C : Category o ℓ e) → (X : Obj[ C ]) → C [ X , X ]
C [1 c ] = (Category.Id C) c

CovariantHomFunctor : {l1 l2 l3 : Level}
  (C : Category l1 l2 l3) →
   Obj[ C ] → Functor C (Sets l2 l3)
CovariantHomFunctor {l1} {l2} {l3} C a =
  record { Obj-func = λ b
              → record {
                     Carrier = C [ a , b ] ;
                     _≈_ = Category._≈_ C ;
                     -- TODO: refinement for readability.
                     isEquivalence = Setoid.isEquivalence (Category.Hom C a b) };
           Arrow-func = λ {c} {c'}
                      → λ (k : C [ c , c' ])
                      → record {
                         _⟨$⟩_ = λ (f : C [ a , c ]) → C [ k ∘ f ] ;
                         cong = λ {f1} {f2} f1≈f2
                           → Category.≈-cong C f1≈f2
                                           (Setoid.refl (Category.Hom C c c')) };
           id = id-proof;
           comp = comp-proof }
 where
   id-proof : {c : Category.Obj C} {f g : C [ a , c ]}
      → C [ f ≈ g ]
      → C [ (C [ C [1 c ] ∘ f ]) ≈ g ] 
   id-proof {c} {f} {g} f≈g =
     begin
       ((C [ C [1 c ] ∘ f ]))
     ≈⟨ Category.unitL C ⟩
       f
     ≈⟨ f≈g ⟩
       g
     ∎
     where open EqR (Category.Hom C a c) -- this ≈ is under Hom[a,c]

   comp-proof : {a : Category.Obj C} {b c : Category.Obj C}
      {f : C [ a , b ]}
      {g : C [ b , c ]}
      {x y : C [ _ , a ]} →
      C [ x ≈ y ] →
      C [ (C [ (C [ g ∘ f ]) ∘ x ]) ≈ (C [ g ∘ (C [ f ∘ y ]) ]) ]
   comp-proof {a} {b} {c} {f} {g} {x} {y} x≈y =
     begin
       (C [ (C [ g ∘ f ]) ∘ x ])
     ≈⟨ Setoid.sym (Category.Hom C _ c) (Category.assoc C) ⟩
       ((C [ g ∘ (C [ f ∘ x ]) ]))
     ≈⟨ Category.≈-cong C (Category.≈-cong C
          x≈y (Setoid.refl (Category.Hom C a b)))
             ((Setoid.refl (Category.Hom C b c))) ⟩
       ((C [ g ∘ (C [ f ∘ y ]) ]))
     ∎
     where open EqR (Category.Hom C _ c)
