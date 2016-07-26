module Definition.CovariantHomFunctor where

open import Definition.Category hiding (_[_,_])
open import Definition.Functor
open import Category.Sets
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)
open PropEq.≡-Reasoning


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
  (C : Category l1 {!!} {!!}) →
   Obj[ C ] → Functor C Sets
CovariantHomFunctor {l1} {l2} {l3} C a =
 record { Obj-func = λ b → C [ a , b ] ;
          Arrow-func = λ {c} {c'}
                     → λ (k : C [ c , c' ])
                     → λ (f : C [ a , c ])
                     →  C [ k ∘ f ] ;
          id   = id-proof;
          comp = {!!} }
 where
   id-proof : {c : Category.Obj C}
     → (λ f → C [ C [1 c ] ∘ f ]) ≡ (Sets [1 (C [ a , c ]) ]) 
   id-proof {c} =
     begin 
       (λ (f : C [ a , c ]) → C [ C [1 c ] ∘ f ])
     ≡⟨ {!!} ⟩ -- unitL (Id b o f) ≈ f cong?subst?
       (λ (f : C [ a , c ]) → f)
     ≡⟨ PropEq.refl ⟩ 
       ((Sets [1 (C [ a , c ]) ]))
     ∎
     where
       hoge : ∀ {A : Set} (f g : A → A) → f ≡ (λ a → a) → g ≡ (λ a → a) → f ≡ g
       hoge f g prff prfg = PropEq.trans prff (PropEq.sym prfg)
   
