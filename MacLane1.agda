{-
  Categories for the Working Mathematician 2nd. Edition in Agda
  by none-Mathematician (>_<)
-}
module MacLane1 where

-- I. Categories, Functors, and Natural Transformations

--- 1. Axiom for Categories (P.7)

--- 2. Categories (P.10)
{-
 A category will mean any interpretation of 
  the category axioms within set theory.
-}

open import Level
open import Relation.Binary

-- (using 8. Hom-Sets notation P.27)
record Category (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    Obj : Set l1
    Hom : Obj → Obj → Set l2 -- arrows
    _o_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    id  : (a : Obj) → Hom a a
   -- In Agda, equality is not trivial, but to be defined everytime.
    _≈_ : {a b : Obj} → Hom a b → Hom a b → Set l3 -- equality of Hom

  infix 1 _≈_
  infixl 10 _o_
  infix 20 id

  -- Axioms
  field
    assoc   : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {k : Hom c d}
            → k o (g o f) ≈ (k o g) o f
    unitL   : {a b : Obj} {f : Hom a b} → id b o f ≈ f
    unitR   : {b c : Obj} {g : Hom b c} → g o id b ≈ g
    -- Property of _≈_
    ≈-equiv : {a b : Obj} → IsEquivalence {l2} {l3} {Hom a b} _≈_ 
    ≈-resp  : {a b c : Obj} {f1 f2 : Hom a b} {g1 g2 : Hom b c} 
            → f1 ≈ f2 → g1 ≈ g2 → g1 o f1 ≈ g2 o f2  
    
-- ==============================
-- Examples of Categories (P.10)
-- ==============================

module Empty-Category where
  data No-Obj : Set where
  data No-Arrow : No-Obj → No-Obj → Set where

  -- 0 is the empty category.
  ZERO : Category zero zero zero
  ZERO = record
           { Obj = No-Obj
           ; Hom = No-Arrow
           ; _o_ = λ {a} {b} {c} _ → λ ()
           ; id = λ ()
           ; _≈_ = λ {a} {b} _ → λ ()
           ; assoc = λ {a} {b} {c} {d} {f} {g} → λ {}
           ; unitL = λ {a} {b} → λ {}
           ; unitR = λ {b} {c} → λ {}
           ; ≈-equiv = λ {a} {b} 
             → record { refl = λ {} ; sym = λ {} ; trans = λ {} }
           ; ≈-resp = λ {a} {b} {c} {f1} {f2} {g1} → λ {}
           }
  -- MEMO: confusing... but Agda tells us an answer by Auto (C-c C-a).
