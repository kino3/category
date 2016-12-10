module Category.NatWithOrder where

open import Definition.Category
open import Data.Nat as N renaming (zero to nzero)
import Relation.Binary.PropositionalEquality as Eq

ℕ≤ : Category zero zero zero
ℕ≤ = record
        { Obj = ℕ
        ; Hom = ℕHom
        ; _o_ = _∘_
        ; Id = x≤x
        ; assoc = λ {a} {b} {c} {d} {f} {g} {k} → assoc-prf f g k
        ; unitL = unitL-prf
        ; unitR = unitR-prf
        ; ≈-cong = cong-prf
        }
  where
    ℕHom : ℕ → ℕ → Setoid zero zero
    ℕHom x y = record { Carrier = x ≤′ y ; _≈_ = Eq._≡_ ; isEquivalence = Eq.isEquivalence }

    _∘_ : {a b c : ℕ} → ℕHom [ b , c ]' → ℕHom [ a , b ]' → ℕHom [ a , c ]'
    ≤′-refl   ∘ ≤′-refl   = ≤′-refl
    ≤′-refl   ∘ ≤′-step g = ≤′-step g
    ≤′-step f ∘ ≤′-refl   = ≤′-step f
    ≤′-step f ∘ ≤′-step g = ≤′-step (f ∘ ≤′-step g)

    x≤x : (a : ℕ) → ℕHom [ a , a ]'
    x≤x a = ≤′-refl

    assoc-prf : {a b c d : ℕ} (f : ℕHom [ a , b ]') (g : ℕHom [ b , c ]') (k : ℕHom [ c , d ]') →
               ℕHom [ k ∘ (g ∘ f) ≈ (k ∘ g) ∘ f ]'
    assoc-prf  ≤′-refl     ≤′-refl     ≤′-refl    = Eq.refl
    assoc-prf  ≤′-refl     ≤′-refl    (≤′-step k) = Eq.refl
    assoc-prf  ≤′-refl    (≤′-step g)  ≤′-refl    = Eq.refl
    assoc-prf  ≤′-refl    (≤′-step g) (≤′-step k) = Eq.refl
    assoc-prf (≤′-step f)  ≤′-refl     ≤′-refl    = Eq.refl
    assoc-prf (≤′-step f)  ≤′-refl    (≤′-step k) = Eq.refl
    assoc-prf (≤′-step f) (≤′-step g)  ≤′-refl    = Eq.refl
    assoc-prf (≤′-step f) (≤′-step g) (≤′-step k) = lemma (assoc-prf (≤′-step f) (≤′-step g) k)
      where
        lemma : ∀ {a b} {f1 f2 : ℕHom [ a , b ]'} → ℕHom [ f1 ≈ f2 ]' → ℕHom [ ≤′-step f1 ≈ ≤′-step f2 ]' 
        lemma {f1 = ≤′-refl}    {≤′-refl}     prf = Eq.refl
        lemma {f1 = ≤′-refl}    {≤′-step f2}  ()
        lemma {f1 = ≤′-step f}  {≤′-refl}     ()
        lemma {f1 = ≤′-step f}  {≤′-step .f} Eq.refl = Eq.refl
    
    unitL-prf : {a b : ℕ} {f : ℕHom [ a , b ]'} → ℕHom [ x≤x b ∘ f ≈ f ]'
    unitL-prf = {!!}
    unitR-prf : {b c : ℕ} {g : ℕHom [ b , c ]'} → ℕHom [ g ∘ x≤x b ≈ g ]'
    unitR-prf = {!!}
    cong-prf : {a b c : ℕ} {f1 f2 : ℕHom [ a , b ]'} {g1 g2 : ℕHom [ b , c ]'} →
              ℕHom [ f1 ≈ f2 ]' → ℕHom [ g1 ≈ g2 ]' → ℕHom [ g1 ∘ f1 ≈ g2 ∘ f2 ]'
    cong-prf = {!!}
