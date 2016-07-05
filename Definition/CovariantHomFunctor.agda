module Definition.CovariantHomFunctor where

open import Definition.Category
open import Definition.Functor
open import Category.Sets
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

-- FIXME : move to Util.Notation?
Obj[_] : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set l1
Obj[ C ] = RawCategory.Obj (Category.definition C)

Hom_[_,_] :
    {l1 l2 l3 : Level}
  → (C : Category l1 l2 l3)
  → Obj[ C ] → Obj[ C ] → Set l2
Hom C [ x , y ] =
  Setoid.Carrier
    (RawCategory.Hom (Category.definition C) x y)

Hom_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y Z} → (Hom C [ Y , Z ]) → (Hom C [ X , Y ])
       → Hom C [ X , Z ]
Hom C [ f ∘ g ] = RawCategory._o_ (Category.definition C) f g

_[1_] : ∀ {o ℓ e}
       → (C : Category o ℓ e) → (X : Obj[ C ]) → Hom C [ X , X ]
C [1 c ] = (RawCategory.Id (Category.definition C)) c

CovariantHomFunctor : {l1 l2 l3 : Level}
  (C : Category l1 zero l3) →
   Obj[ C ] → Functor C Sets
CovariantHomFunctor C a =
  record {
    definition =
      record {
        Obj-func = λ b → Hom C [ a , b ] ;
        Arrow-func = λ k f → Hom C [ k ∘ f ]
      } ;
    axioms =
      record {
        id = id-proof; --id-proof ;
        comp = {!!}
      }
  }
  where
    id-proof : {a b : Obj[ C ]} →
      (λ (f : Hom C [ a , b ]) → (Hom C [ C [1 b ] ∘ f ])) ≡ ((λ f → f))
    id-proof {a} {b} = {!!}

-- in general
{-
p1 : {A : Set} {f : A → A} → (λ f → f) ≡ (λ f → f)
p1 {A} {f} = PropEq.refl

p2 : {A : Set} {f a : A → A} → (λ f → a) → a ≡ f → (λ f → f)
p2 {A} {f} = PropEq.refl
-}

