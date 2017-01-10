module NotationUtil where

open import Definition.Category public

-- Utility for improving readability

Obj[_] : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set l1
Obj[ C ] = Category.Obj C

_[_,_] :
    {l1 l2 l3 : Level}
  → (C : Category l1 l2 l3)
  → Obj[ C ] → Obj[ C ] → Set l2
C [ x , y ] = (Category.Hom C) [ x , y ]'

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y Z} → (C [ Y , Z ]) → (C [ X , Y ])
       → C [ X , Z ]
_[_∘_] = Category._o_ 

_[_≈_] : ∀ {o ℓ e} → (C : Category o ℓ e)
       → ∀ {X Y} → (f g : C [ X , Y ]) → Set e
C [ f ≈ g ] = (Category.Hom C) [ f ≈ g ]'

_[1_] : ∀ {o ℓ e}
       → (C : Category o ℓ e) → (X : Obj[ C ]) → C [ X , X ]
C [1 c ] = (Category.Id C) c

_[_,_]′ :
    {l1 l2 l3 : Level}
  → (C : Category l1 l2 l3)
  → Obj[ C ] → Obj[ C ] → Setoid l2 l3
C [ x , y ]′ = (Category.Hom C) x y

