module Category where

open import Level renaming (zero to l0)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Data.Product renaming (_×_ to _and_)
open import Data.Empty
open import Algebra

record Category (l₁ l₂ l₃ : Level) : Set (suc (l₁ ⊔ l₂ ⊔ l₃)) where
  field
    Obj  : Set l₁
    Hom  : Obj → Obj → Set l₂
    _≈_  : ∀ {A B} → Hom A B → Hom A B → Set l₃
    _∘_  : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id   : (A : Obj) → Hom A A

    -- laws
    associativity : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {k : Hom C D}
      → k ∘ (g ∘ f) ≈ (k ∘ g) ∘ f
    unit-law : ∀ {A B C} {f : Hom A B} {g : Hom B C} 
      → id B ∘ f ≈ f and g ∘ id B ≈ g 
    ≈-eq : IsEquivalence (_≈_ {A = {!!}} {B = {!!}})
 
  infixl 10 _∘_        
  infix   5 _≈_
  infix  20 id

{-
empty : Category l0 l0 l0
empty = record
          { Obj = ⊥
          ; Hom = λ ()
          ; _≈_ = λ x y → ⊥
          ; _∘_ = λ x y → {!!}
          ; id = λ A → {!!}
          ; associativity = {!!}
          ; unit-law = {!!}
          }

open import Data.Unit
C1 : Category l0 l0 l0
C1 = record
       { Obj = ⊤
       ; Hom = λ x y → {!!}
       ; _≈_ = {!!}
       ; _∘_ = {!!}
       ; id = {!!}
       ; associativity = {!!}
       ; unit-law = {!!}
       }

Mon : Category l0 l0 l0
Mon = record
        { Obj = ⊤
        ; Hom = λ t1 t2 → Monoid.Carrier {!!}
        ; _≈_ = {!!}
        ; _∘_ = {!!}
        ; id = {!!}
        ; associativity = {!!}
        ; unit-law = {!!}
        }
-}
