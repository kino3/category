module Category.Sets where

open import Definition.Category
import Relation.Binary.PropositionalEquality as PropEq
import Function.Equality as Feq
import Relation.Binary as B

Sets : (c l : Level) → Category (suc (c ⊔ l)) ((c ⊔ l)) ((c ⊔ l))
Sets c l = record
         { Obj = Setoid c l
         ; Hom = Feq._⇨_
         ; _o_ = Feq._∘_
         ; Id  = λ (X : Setoid c l) → Feq.id
         ; assoc = {!!} --B.IsEquivalence.refl (Setoid.isEquivalence {!!})
         ; unitL = {!!}
         ; unitR = {!!}
         ; ≈-cong = {!!}
         }
{-
Sets = record
         { Obj = Set
         ; Hom = Func
         ; _o_ = λ g f a → g (f a)
         ; Id = λ A a → a
         ; assoc = PropEq.refl
         ; unitL = PropEq.refl
         ; unitR = PropEq.refl
         ; ≈-cong = PropEq.cong₂ (λ b→c a→b a → b→c (a→b a))
         }
   where
     Func : Set → Set → Setoid zero zero
     Func A B = record {
                 Carrier = (A → B) ;
                 _≈_ = PropEq._≡_ ;
                 isEquivalence = PropEq.isEquivalence
                }

-}
{-
record {
     definition = record {
        Obj = Set;
        Hom = Func;
        _o_ = λ {A} {B} {C} g f a
                → g (f a) ;
        Id  = λ A a → a
     } ;
     axioms = record {
        assoc = PropEq.refl ;
        unitL = PropEq.refl ;
        unitR = PropEq.refl ;
        ≈-cong = PropEq.cong₂ (λ b→c a→b a → b→c (a→b a)) 
     }
 }

-}
