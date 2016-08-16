module Theorem.Yoneda where

open import Definition.Category
open import Definition.Functor
open import Definition.NaturalTransformation
open import Definition.CovariantHomFunctor
open import Category.Sets
import Function.Bijection as FB

Yoneda-lemma : ∀ {l1 l2 l3} → -- D is small?
               {D : Category l1 l2 l3} {K : D ⟶ (Sets l2 l3)}
               {r : Category.Obj D} →
               FB.Bijection {l3} {l3}
                 {!!} {-
                 (record { Carrier = (D [ r ,-]) ∸> K ; --TODO infix level
                           _≈_ = {!!} ;
                           isEquivalence = {!!} }) -}
                 ((Functor.fo K) r)
Yoneda-lemma = {!!}
