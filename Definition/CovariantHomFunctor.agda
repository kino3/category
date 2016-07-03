module Definition.CovariantHomFunctor where

open import Definition.Category
open import Definition.Functor
open import Category.Sets

-- FIXME : move to Util.Notation?
Obj[_] : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set l1
Obj[ C ] = RawCategory.Obj (Category.definition C)

_′ : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set l1 → Set l1 → Set l2
(C ′) a b = ? --(RawCategory.Hom (Category.definition C)) ? ?

CovariantHomFunctor : {l1 l2 l3 : Level}
  (C : Category l1 l2 l3) →
   Obj[ C ] → Functor C Sets
CovariantHomFunctor C a =
  record {
    definition =
      record {
        Obj-func = λ b → {!!} [ a , b ] ;
        Arrow-func = {!!}
      } ;
    axioms =
      record {
        id = {!!} ;
        comp = {!!}
      }
  }

