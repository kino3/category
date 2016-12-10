module Category.One where

open import Definition.Category
import Relation.Binary.PropositionalEquality as Eq

One : Category zero zero zero
One = record
        { Obj = Obj1
        ; Hom = Hom1'
        ; _o_ = _∘_
        ; Id = id1
        ; assoc = assoc-prf
        ; unitL = unitL-prf
        ; unitR = unitR-prf
        ; ≈-cong = cong-prf
        }
  where
    data Obj1 : Set where
      * : Obj1

    data Hom1 : Obj1 → Obj1 → Set where
      *→* : Hom1 * *

    Hom1' : Obj1 → Obj1 → Setoid zero zero
    Hom1' * * = record { Carrier = Hom1 * * ; _≈_ = Eq._≡_ ; isEquivalence = Eq.isEquivalence }

    _∘_ : {a b c : Obj1} → Hom1' [ b , c ]' → Hom1' [ a , b ]' → Hom1' [ a , c ]'
    _∘_ {*} {*} {*} f g = *→*

    id1 : (a : Obj1) → Hom1' [ a , a ]'
    id1 * = *→*

    assoc-prf : {a b c d : Obj1} {f : Hom1' [ a , b ]'} {g : Hom1' [ b , c ]'} {k : Hom1' [ c , d ]'} →
                Hom1' [ (k ∘ (g ∘ f)) ≈ ((k ∘ g) ∘ f) ]'
    assoc-prf {*} {*} {*} {*} {*→*} {*→*} {*→*} = Eq.refl

    unitL-prf : {a b : Obj1} {f : Hom1' [ a , b ]'} → Hom1' [ id1 b ∘ f ≈ f ]'
    unitL-prf {*} {*} {*→*} = Eq.refl

    unitR-prf : {b c : Obj1} {g : Hom1' [ b , c ]'} → Hom1' [ g ∘ id1 b ≈ g ]'
    unitR-prf {*} {*} {*→*} = Eq.refl

    cong-prf : {a b c : Obj1} {f1 f2 : Hom1' [ a , b ]'} {g1 g2 : Hom1' [ b , c ]'} →
               Hom1' [ f1 ≈ f2 ]' → Hom1' [ g1 ≈ g2 ]' → Hom1' [ g1 ∘ f1 ≈ g2 ∘ f2 ]'
    cong-prf {*} {*} {*} {*→*} {*→*} {*→*} {*→*} Eq.refl Eq.refl = Eq.refl
