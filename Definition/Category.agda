module Definition.Category where
open import Level public
open import Relation.Binary using (Setoid) public
import Relation.Binary as B

_[_,_]' : ∀ {a b c} {X : Set a} → (h : X → X → Setoid b c) → X → X → Set b
h [ x , y ]' = Setoid.Carrier (h x y)

record Category (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    Obj : Set l1
    Hom : Obj → Obj → Setoid l2 l3
    _o_ : {a b c : Obj} → Hom [ b , c ]' → Hom [ a , b ]' → Hom [ a , c ]'
    Id  : (a : Obj) → Hom [ a , a ]'

  -- for convenience  
  _≈_ : {a b : Obj} → Hom [ a , b ]' → Hom [ a , b ]' → Set l3
  _≈_ {a} {b} p q = Setoid._≈_ (Hom a b) p q

  field
    assoc   : {a b c d : Obj} {f : Hom [ a , b ]'} 
              {g : Hom [ b , c ]'} {k : Hom [ c , d ]'}
            → (k o (g o f)) ≈ ((k o g) o f)
    unitL   : {a b : Obj} {f : Hom [ a , b ]'} → (Id b o f) ≈ f
    unitR   : {b c : Obj} {g : Hom [ b , c ]'} → (g o Id b) ≈ g
    ≈-cong  : ∀ {a b c} {f1 f2 : Hom [ a , b ]'} {g1 g2 : Hom [ b , c ]'} 
            → f1 ≈ f2 → g1 ≈ g2 → (g1 o f1) ≈ (g2 o f2)  

  infix   1 _≈_
  infixl 10 _o_
  infix  20 Id

-- Utility for improving readability

Obj[_] : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set l1
Obj[ C ] = Category.Obj C

_[_,_] :
    {l1 l2 l3 : Level}
  → (C : Category l1 l2 l3)
  → Obj[ C ] → Obj[ C ] → Set l2
C [ x , y ] =
  Setoid.Carrier
    (Category.Hom C x y)

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y Z} → (C [ Y , Z ]) → (C [ X , Y ])
       → C [ X , Z ]
_[_∘_] = Category._o_ 
--syntax Category._o_ = _[_∘_] 

_[_≈_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y} → (f g : C [ X , Y ]) → Set e
_[_≈_] = Category._≈_

_[1_] : ∀ {o ℓ e}
       → (C : Category o ℓ e) → (X : Obj[ C ]) → C [ X , X ]
C [1 c ] = (Category.Id C) c

_[_,_]′ :
    {l1 l2 l3 : Level}
  → (C : Category l1 l2 l3)
  → Obj[ C ] → Obj[ C ] → Setoid l2 l3
C [ x , y ]′ = (Category.Hom C) x y

--syntax (Category.Hom C) x y = C [ x , y ]′
