module Definition.Category where
open import Level public
open import Relation.Binary using (Setoid) public
import Relation.Binary as B

_[_,_]' : ∀ {a b c} {X : Set a} → (h : X → X → Setoid b c) → X → X → Set b
h [ x , y ]' = Setoid.Carrier (h x y)

_[_≈_]' : ∀ {a b c} {O : Set a} → (h : O → O → Setoid b c)
       → ∀ {X Y} → h [ X , Y ]' → h [ X , Y ]' → Set c
_[_≈_]' {a} {b} {c} {O} h {X} {Y} f g = Setoid._≈_ (h X Y) f g

record Category (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    Obj : Set l1
    Hom : Obj → Obj → Setoid l2 l3
    _o_ : {a b c : Obj} → Hom [ b , c ]' → Hom [ a , b ]' → Hom [ a , c ]'
    Id  : (a : Obj) → Hom [ a , a ]'

    assoc   : {a b c d : Obj} {f : Hom [ a , b ]'} 
              {g : Hom [ b , c ]'} {k : Hom [ c , d ]'}
            → Hom [ (k o (g o f)) ≈ ((k o g) o f) ]'
    unitL   : {a b : Obj} {f : Hom [ a , b ]'} → Hom [ (Id b o f) ≈ f ]'
    unitR   : {b c : Obj} {g : Hom [ b , c ]'} → Hom [ (g o Id b) ≈ g ]'
    ≈-cong  : ∀ {a b c} {f1 f2 : Hom [ a , b ]'} {g1 g2 : Hom [ b , c ]'} 
            → Hom [ f1 ≈ f2 ]' → Hom [ g1 ≈ g2 ]' → Hom [ (g1 o f1) ≈ (g2 o f2) ]'  

  infixl 10 _o_
  infix  20 Id


