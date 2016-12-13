module Category.Four where

open import Definition.Category
open import Relation.Binary.PropositionalEquality

data Obj4 : Set where
  o1 : Obj4
  o2 : Obj4
  o3 : Obj4
  o4 : Obj4
  
data Hom4 : Obj4 → Obj4 → Set where
  1→2 : Hom4 o1 o2
  1→3 : Hom4 o1 o3
  1→4 : Hom4 o1 o4 
  2→3 : Hom4 o2 o3
  2→4 : Hom4 o2 o4
  3→4 : Hom4 o3 o4
  id  : (x : Obj4) → Hom4 x x

_∘_ : {a b c : Obj4} → Hom4 b c → Hom4 a b → Hom4 a c
2→3 ∘ 1→2 = 1→3
2→4 ∘ 1→2 = 1→4
3→4 ∘ 1→3 = 1→4
3→4 ∘ 2→3 = 2→4
id x ∘ g = g
f ∘ id x = f

Hom4' : Obj4 → Obj4 → Setoid zero zero
Hom4' = λ x y → record { Carrier = Hom4 x y ; _≈_ = _≡_ ; isEquivalence = isEquivalence }

Four : Category zero zero zero
Four = record
          { Obj = Obj4
          ; Hom = Hom4'
          ; _o_ = _∘_
          ; Id = id
          ; assoc = λ {w} {x} {y} {z} {f} {g} {k} → assoc-prf {w} {x} {y} {z} {f} {g} {k} 
          ; unitL = unitL-prf
          ; unitR = unitR-prf
          ; ≈-cong = cong-prf
          }
  where
    unitL-prf : {x y : Obj4} {f : Hom4' [ x , y ]'} → Hom4' [ id y ∘ f ≈ f ]'
    unitL-prf {f = 1→2} = refl
    unitL-prf {f = 1→3} = refl
    unitL-prf {f = 1→4} = refl
    unitL-prf {f = 2→3} = refl
    unitL-prf {f = 2→4} = refl
    unitL-prf {f = 3→4} = refl
    unitL-prf {f = id _} = refl

    unitR-prf : {y z : Obj4} {g : Hom4' [ y , z ]'} → Hom4' [ g ∘ id y ≈ g ]'
    unitR-prf {g = 1→2} = refl
    unitR-prf {g = 1→3} = refl
    unitR-prf {g = 1→4} = refl
    unitR-prf {g = 2→3} = refl
    unitR-prf {g = 2→4} = refl
    unitR-prf {g = 3→4} = refl
    unitR-prf {g = id _} = refl

    cong-prf  : {x y z : Obj4} {f1 f2 : Hom4' [ x , y ]'} {g1 g2 : Hom4' [ y , z ]'} →
                Hom4' [ f1 ≈ f2 ]' → Hom4' [ g1 ≈ g2 ]' → Hom4' [ g1 ∘ f1 ≈ g2 ∘ f2 ]'
    cong-prf refl refl = refl

    assoc-prf : {w x y z : Obj4} {f : Hom4' [ w , x ]'} {g : Hom4' [ x , y ]'}
                {k : Hom4' [ y , z ]'} → Hom4' [ k ∘ (g ∘ f) ≈ (k ∘ g) ∘ f ]'
    assoc-prf {f = 1→2} {2→3} {3→4} = refl
    assoc-prf {f = 1→2} {2→3} {id .o3} = refl
    assoc-prf {f = 1→2} {2→4} {id .o4} = refl
    assoc-prf {f = 1→2} {id .o2} {2→3} = refl
    assoc-prf {f = 1→2} {id .o2} {2→4} = refl
    assoc-prf {f = 1→2} {id .o2} {id .o2} = refl
    assoc-prf {f = 1→3} {3→4} {id .o4} = refl
    assoc-prf {f = 1→3} {id .o3} {3→4} = refl
    assoc-prf {f = 1→3} {id .o3} {id .o3} = refl
    assoc-prf {f = 1→4} {id .o4} {id .o4} = refl
    assoc-prf {f = 2→3} {3→4} {id .o4} = refl
    assoc-prf {f = 2→3} {id .o3} {3→4} = refl
    assoc-prf {f = 2→3} {id .o3} {id .o3} = refl
    assoc-prf {f = 2→4} {id .o4} {id .o4} = refl
    assoc-prf {f = 3→4} {id .o4} {id .o4} = refl
    assoc-prf {f = id .o1} {1→2} {2→3} = refl
    assoc-prf {f = id .o1} {1→2} {2→4} = refl
    assoc-prf {f = id .o1} {1→2} {id .o2} = refl
    assoc-prf {f = id .o1} {1→3} {3→4} = refl
    assoc-prf {f = id .o1} {1→3} {id .o3} = refl
    assoc-prf {f = id .o1} {1→4} {id .o4} = refl
    assoc-prf {f = id .o2} {2→3} {3→4} = refl
    assoc-prf {f = id .o2} {2→3} {id .o3} = refl
    assoc-prf {f = id .o2} {2→4} {id .o4} = refl
    assoc-prf {f = id .o3} {3→4} {id .o4} = refl
    assoc-prf {f = id .o1} {id .o1} {1→2} = refl
    assoc-prf {f = id .o1} {id .o1} {1→3} = refl
    assoc-prf {f = id .o1} {id .o1} {1→4} = refl
    assoc-prf {f = id .o2} {id .o2} {2→3} = refl
    assoc-prf {f = id .o2} {id .o2} {2→4} = refl
    assoc-prf {f = id .o3} {id .o3} {3→4} = refl
    assoc-prf {f = id _} {id _} {id _} = refl


