module Theorem.Yoneda where

open import NotationUtil

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

Proposition1
  {l1} {l2} {l3} {m1} {m2} {m3}
  {D} {C} {c} S {r} {u} univ d' =
  record { to = record {
                   _⟨$⟩_ = λ f' → C [ Functor.fa S f' ∘ u ] ;
                   cong  = λ i≈j → Functor.≈-resp S {!!} {!!} {!!} --λ {i} {j} i≈j → {!!} --Functor.≈-resp S {!!} {!!} {!!}
                };
           bijective = record {
                         injective = {!!} ;
                         surjective = {!!} } }
record representation
  (D : Category zero zero zero)
  (K : D ⟶ (Sets zero zero))
  : Set (suc (suc zero)) where
  field
    r : Category.Obj D
    ψ : (D [ r ,-]) ≅ K
-- TODO: level may be incorrect.          

postulate Proposition2 : Set

import Relation.Binary.PropositionalEquality as Eq using (_≡_;isEquivalence)
{-
Yoneda-lemma : {D : Category zero zero zero}
               (K : D ⟶ (Sets zero zero))
               (r : Category.Obj D) →
               FB.Bijection 
                 (record { Carrier = (D [ r ,-]) ∸> K ;
                           _≈_ = Eq._≡_ ;
                           isEquivalence = Eq.isEquivalence}) 
                 ((Functor.fo K) r)
Yoneda-lemma K r = record {
  to = record { _⟨$⟩_ = λ α → {!!} ;
                cong  = {!!} } ;
  bijective = record { injective = {!!} ; surjective = {!!} } }

-}
