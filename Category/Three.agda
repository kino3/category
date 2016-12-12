module Category.Three where

open import Definition.Category
open import Relation.Binary.PropositionalEquality

data Obj3 : Set where
  a : Obj3
  b : Obj3
  c : Obj3
data Hom3 : Obj3 → Obj3 → Set where
  a→b : Hom3 a b
  b→c : Hom3 b c
  a→c : Hom3 a c
  id  : (x : Obj3) → Hom3 x x
Hom3' : Obj3 → Obj3 → Setoid zero zero
Hom3' = λ x y → record { Carrier = Hom3 x y ; _≈_ = _≡_ ; isEquivalence = isEquivalence }

_∘_ : {a b c : Obj3} → Hom3' [ b , c ]' → Hom3' [ a , b ]' → Hom3' [ a , c ]'
b→c  ∘ a→b  = a→c
f    ∘ id _ = f
id _ ∘ g    = g

Three : Category zero zero zero
Three = record
          { Obj = Obj3
          ; Hom = Hom3'
          ; _o_ = _∘_
          ; Id = id
          ; assoc = λ {w} {x} {y} {z} {f} {g} {k} → assoc-prf {w} {x} {y} {z} {f} {g} {k} 
          ; unitL = unitL-prf
          ; unitR = unitR-prf
          ; ≈-cong = cong-prf
          }
  where

    assoc-prf : {w x y z : Obj3} {f : Hom3' [ w , x ]'} {g : Hom3' [ x , y ]'}
                {k : Hom3' [ y , z ]'} → Hom3' [ k ∘ (g ∘ f) ≈ (k ∘ g) ∘ f ]'
    assoc-prf {f = a→b} {b→c} {id .c}   = refl
    assoc-prf {f = a→b} {id .b} {b→c}   = refl
    assoc-prf {f = a→b} {id .b} {id .b} = refl
    assoc-prf {f = b→c} {id .c} {id .c} = refl
    assoc-prf {f = a→c} {id .c} {id .c} = refl
    assoc-prf {f = id .a} {a→b} {b→c}   = refl
    assoc-prf {f = id .a} {a→b} {id .b} = refl
    assoc-prf {f = id .b} {b→c} {id .c} = refl
    assoc-prf {f = id .a} {a→c} {id .c} = refl
    assoc-prf {f = id .a} {id .a} {a→b} = refl
    assoc-prf {f = id .b} {id .b} {b→c} = refl
    assoc-prf {f = id .a} {id .a} {a→c} = refl
    assoc-prf {f = id _} {id _} {id _}  = refl

    unitL-prf : {x y : Obj3} {f : Hom3' [ x , y ]'} → Hom3' [ id y ∘ f ≈ f ]'
    unitL-prf {f = a→b} = refl
    unitL-prf {f = b→c} = refl
    unitL-prf {f = a→c} = refl
    unitL-prf {f = id _} = refl
    unitR-prf : {y z : Obj3} {g : Hom3' [ y , z ]'} → Hom3' [ g ∘ id y ≈ g ]'
    unitR-prf {g = a→b} = refl
    unitR-prf {g = b→c} = refl
    unitR-prf {g = a→c} = refl
    unitR-prf {g = id _} = refl
    cong-prf  : {x y z : Obj3} {f1 f2 : Hom3' [ x , y ]'} {g1 g2 : Hom3' [ y , z ]'} →
                Hom3' [ f1 ≈ f2 ]' → Hom3' [ g1 ≈ g2 ]' → Hom3' [ g1 ∘ f1 ≈ g2 ∘ f2 ]'
    cong-prf refl refl = refl
