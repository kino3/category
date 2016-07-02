module Category.Sets where

open import Definition.Category
import Relation.Binary.PropositionalEquality as PropEq

-- move?
--[_] : {l m : Level} → Setoid l m → Set l
--[ record { Carrier = Carrier ; _≈_ = _≈_ ; isEquivalence = isEquivalence } ] = Carrier

Sets : Category (suc zero) zero zero
Sets = record {
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
        unitR = PropEq.refl
     }
 }
   where
     Func : Set → Set → Setoid zero zero
     Func A B = record {
                 Carrier = (A → B) ;
                 _≈_ = PropEq._≡_ ;
                 isEquivalence = PropEq.isEquivalence
                }

