{-
  Categories for the Working Mathematician 2nd. Edition in Agda
  by none-Mathematician (>_<)
-}
module MacLane1 where

open import Level
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality


-- I. Categories, Functors, and Natural Transformations

--- 1. Axiom for Categories (P.7)

--- 2. Categories (P.10)
{-
 A category will mean any interpretation of 
  the category axioms within set theory.
-}

-- (using 8. Hom-Sets notation P.27)
record Category (l1 l2 l3 : Level) : Set (suc (l1 ⊔ l2 ⊔ l3)) where
  field
    Obj : Set l1
    Hom : Obj → Obj → Set l2 -- arrows
    _o_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    id  : (a : Obj) → Hom a a
   -- In Agda, equality is not trivial, but to be defined everytime.
    _≈_ : {a b : Obj} → Hom a b → Hom a b → Set l3 -- equality of Hom

  -- Axioms
  field
    assoc   : {a b c d : Obj} {f : Hom a b} {g : Hom b c} {k : Hom c d}
            → k o (g o f) ≈ (k o g) o f
    unitL   : {a b : Obj} {f : Hom a b} → id b o f ≈ f
    unitR   : {b c : Obj} {g : Hom b c} → g o id b ≈ g
    -- Property of _≈_
    ≈-equiv : {a b : Obj} → IsEquivalence {l2} {l3} {Hom a b} _≈_ 
    ≈-cong  : {a b c : Obj} {f1 f2 : Hom b c} {g1 g2 : Hom a b} 
            → f1 ≈ f2 → g1 ≈ g2 → f1 o g1 ≈ f2 o g2  

  infix   1 _≈_
  infixl 10 _o_
  infix  20 id
    
-- ==============================
-- Examples of Categories (P.10)
-- ==============================

module Category0 where
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
           ; ≈-cong = λ {a} {b} {c} {f1} {f2} {g1} → λ {}
           }
  -- MEMO: confusing... but Agda tells us an answer by Auto (C-c C-a).

--open Category0 public

module Category1 where

  data Obj1 : Set where
    * : Obj1

  data Arrow1 : Obj1 → Obj1 → Set where
    *→* : Arrow1 * *

  _∘_ : {a b c : Obj1} → Arrow1 b c → Arrow1 a b → Arrow1 a c
  *→* ∘ *→* = *→*

  id : (a : Obj1) → Arrow1 a a
  id * = *→*

  -- 1 is the category with one object and one (identity) arrow;
  ONE : Category zero zero zero
  ONE = record
          { Obj = Obj1
          ; Hom = Arrow1
          ; _o_ = _∘_
          ; id = id
          ; _≈_ = _≡_
          ; assoc = assoc-proof
          ; unitL = unitL-proof
          ; unitR = unitR-proof
          ; ≈-equiv = isEquivalence
          ; ≈-cong = λ f1=f2 g1=g2 → cong₂ _∘_ f1=f2 g1=g2 
          }
    where
      assoc-proof : {a b c d : Obj1} {f : Arrow1 a b} 
                    {g : Arrow1 b c} {k : Arrow1 c d} →
                     (k ∘ (g ∘ f)) ≡ ((k ∘ g) ∘ f)
      assoc-proof {*}{*}{*}{*} {*→*}{*→*}{*→*} = refl

      unitL-proof : {a b : Obj1} {f : Arrow1 a b} → (id b ∘ f) ≡ f
      unitL-proof {*}{*} {*→*} = refl

      unitR-proof : {b c : Obj1} {g : Arrow1 b c} → (g ∘ id b) ≡ g
      unitR-proof {*}{*} {*→*} = refl

--open Category1 public

module Category2 where

  data Obj2 : Set where
    *1 : Obj2
    *2 : Obj2

  data Arrow2 : Obj2 → Obj2 → Set where
    1→2 : Arrow2 *1 *2
    id1 : Arrow2 *1 *1
    id2 : Arrow2 *2 *2

  _∘_ : {a b c : Obj2} → Arrow2 b c → Arrow2 a b → Arrow2 a c
  1→2 ∘ id1 = 1→2
  id1 ∘ id1 = id1
  id2 ∘ 1→2 = 1→2
  id2 ∘ id2 = id2

  id : (a : Obj2) → Arrow2 a a
  id *1 = id1
  id *2 = id2 

  TWO : Category zero zero zero
  TWO = record
          { Obj = Obj2
          ; Hom = Arrow2
          ; _o_ = _∘_
          ; id = id
          ; _≈_ = _≡_
          ; assoc = λ {a b c d : Obj2} {f : Arrow2 a b} {g : Arrow2 b c} {k : Arrow2 c d} 
                    → assoc-proof {a}{b}{c}{d}{f}{g}{k} -- I wonder why I should write this {}s way...
          ; unitL = unitL-proof
          ; unitR = unitR-proof
          ; ≈-equiv = isEquivalence
          ; ≈-cong = λ f1=f2 g1=g2 → cong₂ _∘_ f1=f2 g1=g2
          }
   where
     assoc-proof : {a b c d : Obj2}{f : Arrow2 a b} {g : Arrow2 b c}
                   {k : Arrow2 c d} → k ∘ (g ∘ f) ≡ (k ∘ g) ∘ f
     assoc-proof {*1} {*1} {*1} {*1} {id1} {id1} {id1} = refl
     assoc-proof {*1} {*1} {*1} {*2} {id1} {id1} {1→2} = refl
     assoc-proof {*1} {*1} {*2} {*1} {id1} {1→2} {()}
     assoc-proof {*1} {*1} {*2} {*2} {id1} {1→2} {id2} = refl
     assoc-proof {*1} {*2} {*1} {*1} {1→2} {()}
     assoc-proof {*1} {*2} {*1} {*2} {1→2} {()}
     assoc-proof {*1} {*2} {*2} {*1} {1→2} {id2} {()}
     assoc-proof {*1} {*2} {*2} {*2} {1→2} {id2} {id2} = refl
     assoc-proof {*2} {*1} {*1} {*1} {()}
     assoc-proof {*2} {*1} {*1} {*2} {()}
     assoc-proof {*2} {*1} {*2} {*1} {()}
     assoc-proof {*2} {*1} {*2} {*2} {()}
     assoc-proof {*2} {*2} {*1} {*1} {id2} {()}
     assoc-proof {*2} {*2} {*1} {*2} {id2} {()}
     assoc-proof {*2} {*2} {*2} {*1} {id2} {id2} {()}
     assoc-proof {*2} {*2} {*2} {*2} {id2} {id2} {id2}  = refl

     unitL-proof : {a b : Obj2} {f : Arrow2 a b} → id b ∘ f ≡ f
     unitL-proof {b = *1} {f = id1} = refl
     unitL-proof {b = *2} {f = 1→2} = refl
     unitL-proof {b = *2} {f = id2} = refl

     unitR-proof : {b c : Obj2} {g : Arrow2 b c} → g ∘ id b ≡ g
     unitR-proof {c = *1} {g = id1} = refl
     unitR-proof {c = *2} {g = 1→2} = refl
     unitR-proof {c = *2} {g = id2} = refl

module Category3 where
  
  data Obj3 : Set where
    *1 *2 *3 : Obj3

  data Arrow3 : Obj3 → Obj3 → Set where
    1→2 : Arrow3 *1 *2
    2→3 : Arrow3 *2 *3
    1→3 : Arrow3 *1 *3
    id  : (a : Obj3) → Arrow3 a a -- abbriviation

  _∘_ : {a b c : Obj3} → Arrow3 b c → Arrow3 a b → Arrow3 a c
  g ∘ id a = g
  id b ∘ f = f
  2→3 ∘ 1→2 = 1→3

  THREE : Category zero zero zero
  THREE = record
            { Obj = Obj3
            ; Hom = Arrow3
            ; _o_ = _∘_
            ; id = id
            ; _≈_ = _≡_
            ; assoc = λ {a b c d : Obj3} {f : Arrow3 a b} {g : Arrow3 b c} {k : Arrow3 c d} 
                      → assoc-proof {a} {b} {c} {d} {f} {g} {k}
            ; unitL = unitL-proof
            ; unitR = unitR-proof
            ; ≈-equiv = isEquivalence
            ; ≈-cong = λ f1=f2 g1=g2 → cong₂ _∘_ f1=f2 g1=g2
            }
    where
      assoc-proof :  {a b c d : Obj3} {f : Arrow3 a b} {g : Arrow3 b c}
                     {k : Arrow3 c d} → k ∘ (g ∘ f) ≡ (k ∘ g) ∘ f
      assoc-proof {f = 1→2} {2→3} {id .*3} = refl
      assoc-proof {f = 1→2} {id .*2} = refl
      assoc-proof {f = 2→3} {id .*3} = refl
      assoc-proof {f = 1→3} {id .*3} = refl
      assoc-proof {f = id .*1} {1→2} = refl
      assoc-proof {f = id .*2} {2→3} = refl
      assoc-proof {f = id .*1} {1→3} = refl
      assoc-proof {f = id .*1} {id .*1} {1→2} = refl
      assoc-proof {f = id .*2} {id .*2} {2→3} = refl
      assoc-proof {f = id .*1} {id .*1} {1→3} = refl
      assoc-proof {f = id ._} {id ._} {id ._} = refl

      unitL-proof : {a b : Obj3} {f : Arrow3 a b} → id b ∘ f ≡ f
      unitL-proof {b = *1} {id .*1} = refl
      unitL-proof {b = *2} {1→2}    = refl
      unitL-proof {b = *2} {id .*2} = refl
      unitL-proof {b = *3} {2→3}    = refl
      unitL-proof {b = *3} {1→3}    = refl
      unitL-proof {b = *3} {id .*3} = refl

      unitR-proof : {b c : Obj3} {g : Arrow3 b c} → g ∘ id b ≡ g
      unitR-proof {c = *1} = refl
      unitR-proof {c = *2} = refl
      unitR-proof {c = *3} = refl

module Monoid-is-Category where

  record * : Set where

  open import Algebra
  open import Algebra.Structures
  open import Algebra.FunctionProperties
  open import Data.Product
  open import Relation.Binary.Core

  postulate
    x : Monoid zero zero

  -- if x is a Monoid, x is also a Category. (described as M below.)
  M : Category zero zero zero
  M = record
        { Obj = *
        ; Hom = λ a b → Monoid.Carrier x
        ; _o_ = Monoid._∙_ x
        ; id = λ a → Monoid.ε x
        ; _≈_ = Monoid._≈_ x
        ; assoc = λ {a} {b} {c} {d} {f} {g} {k} 
          → IsEquivalence.sym (IsSemigroup.isEquivalence (IsMonoid.isSemigroup (Monoid.isMonoid x))) 
                              (IsSemigroup.assoc (IsMonoid.isSemigroup (Monoid.isMonoid x)) k g f)
        ; unitL = λ {a} {b} {f} → proj₁ (IsMonoid.identity (Monoid.isMonoid x)) f
        ; unitR = λ {b} {c} {g} → proj₂ (IsMonoid.identity (Monoid.isMonoid x)) g
        ; ≈-equiv = IsSemigroup.isEquivalence (IsMonoid.isSemigroup (Monoid.isMonoid x))
        ; ≈-cong = IsSemigroup.∙-cong (IsMonoid.isSemigroup (Monoid.isMonoid x))
        }

open import Function using (_∘′_;_∋_)
Sets : Category (suc zero) zero zero
Sets = record
        { Obj = Set zero
        ; Hom = λ A B → (A → B)
        ; _o_ = λ g f → g ∘′ f
        ; id = λ A a → a
        ; _≈_ = _≡_
        ; assoc = refl
        ; unitL = refl
        ; unitR = refl
        ; ≈-equiv = isEquivalence
        ; ≈-cong = cong₂ (λ g f → g ∘′ f)
        }

{-
open import Relation.Binary using (REL)
open import Data.Product renaming (_,_ to _&_)
ℝel : Category (suc zero) (suc zero) (suc zero)
ℝel = record
        { Obj = Set zero
        ; Hom = λ X Y → REL X Y zero
        ; _o_ = _∘ᵣ_
        ; id = λ A → RelId {A}
        ; _≈_ = _≡_
        ; assoc = {!!}
        ; unitL = {!!} --unitL-proof
        ; unitR = {!!}
        ; ≈-equiv = isEquivalence
        ; ≈-cong = {!!}
        }
  where
    _∘ᵣ_ : {X Y Z : Set} {y : Y} → REL Y Z zero → REL X Y zero → REL X Z zero 
    _∘ᵣ_ {X} {Y} {Z} {y} S R x z = S y z × R x y
    {-
    data _∘ᵣ_ {X Y Z : Set} (S : REL Y Z zero) (R : REL X Y zero) (x : X) (z : Z) : Set where
      Comp : {y : Y} {s : S y z} {r : R x y} → (S ∘ᵣ R) x z
    -}
    data RelId {A : Set} (a : A) : A → Set where
      Rel-refl : RelId a a

    unitL-proof : {A B : Set} {f : REL A B zero} → RelId ∘ᵣ f ≡ f
    unitL-proof {A} {B} {f} = {!!}
-}

--------------------------------
-- 3. Functors
--------------------------------

{-
  syntax sugars to improve readability
    from : https://github.com/copumpkin/categories
-}
_[_,_] : ∀ {o ℓ e} → (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category.Hom

_[_≈_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
_[_≈_] = Category._≈_

_[_o_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_o_] = Category._o_
-- end of syntax sugars --

record Functor 
  {l1 l2 l3 m1 m2 m3 : Level} 
  (C : Category l1 l2 l3) 
  (B : Category m1 m2 m3) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where

  -- syntax sugars
  private module C = Category C
  private module B = Category B

  field
    -- two suitably related functions.
    Tₒ : C.Obj → B.Obj
    Tₕ : {c c' : C.Obj} → C [ c , c' ] → B [ (Tₒ c) , (Tₒ c') ]
    -- axioms of Functor
    prop1 : {c : C.Obj} → B [ (Tₕ (C.id c)) ≈ (B.id (Tₒ c)) ]
    prop2 : {a b c : C.Obj}{f : C [ a , b ]}{g : C [ b , c ]} 
            → B [ Tₕ(C [ g o f ]) ≈ B [ Tₕ(g) o Tₕ(f) ] ]
    -- additional axiom for _≈_
    prop3 : ∀ {a b} {f g : C [ a , b ]} → C [ f ≈ g ] → B [ Tₕ f ≈ Tₕ g ]

--------------------------------
-- 4. Natural Transformations
--------------------------------
record _⇴_
  {l1 l2 l3 m1 m2 m3 : Level} 
  {C : Category l1 l2 l3} 
  {B : Category m1 m2 m3} 
  (S T : Functor C B) : Set (suc (l1 ⊔ l2 ⊔ l3 ⊔ m1 ⊔ m2 ⊔ m3)) where
  private module S = Functor S
  private module T = Functor T
  private module C = Category C
  private module B = Category B
  
  field
    τ : (c : C.Obj) → B [ S.Tₒ c , T.Tₒ c ]
    -- commutative diagram
    prop1 : {c c' : C.Obj} {f : C [ c , c' ]} 
            → B [ B [ τ c' o S.Tₕ f ] ≈ B [ T.Tₕ f o τ c ] ]

--------------------------------
-- 5. Monics, Epis, and Zeros
--------------------------------
