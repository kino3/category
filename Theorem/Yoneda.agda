module Theorem.Yoneda where

open import Definition.Category
open import Definition.Functor
open import Definition.NaturalTransformation
open import Definition.CovariantHomFunctor
open import Category.Sets
import Function.Bijection as FB

open import Definition.Universal
open import Data.Product
-- on MacLane P.59


_iff_ : ∀ {m n} → Set m → Set n → Set _
P iff Q = (P → Q) × (Q → P)

Proposition1 : ∀ {l1 l2 l3 m1 m2 m3} →
  {D : Category l1 l2 l3}
  {C : Category m1 m2 m3}
  {c : Obj[ C ]}
  (S : D ⟶ C) 
  {r : Obj[ D ]}
  {u : C [ c , (Functor.fo S) r ]} →
  (universal-from c to S) r u →
  ( (d : Obj[ D ]) → 
    FB.Bijection (D [ r , d ]′) (C [ c , (Functor.fo S) d ]′) )
Proposition1 S (universality d f prf) d' =
  record { to = record {
                   _⟨$⟩_ = {!!} ;
                   cong  = {!!} } ;
           bijective = {!!} }

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
