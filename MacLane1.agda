module MacLane1 where

-- I. Categories, Functors, and Natural Transformations

--- 1. Axiom for Categories (P.7)

--- 2. Categories (P.10)
---- A category will mean any interpretation of the category axioms within set theory.
open import Level

record Category : Set1 where
  field
    O : Set
    A : O → O → Set

  Objects = O
  Arrows  = A

  dom : {a b : O} → A a b → O
  dom {a} {b} f = a
  cod : {a b : O} → A a b → O
  cod {a} {b} f = b
  
  field
    id : (a : O) → A a a
    _×_ : {a b c : O} → A b c → A a b → A a c
