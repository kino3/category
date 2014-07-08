module Awodey1 where
{-
Reference::
http://ie.u-ryukyu.ac.jp/~kono/lecture/software/Agda/index.html
https://github.com/konn/category-agda
-}

{-===================================================
 A formalization of Awodey's Book "Category Theory"
 Second Edition
===================================================-}
open import Level

-------------------------------------
-- 1.2 Functions of sets
-------------------------------------

-- P.3
func : {l : Level} → (A B : Set l) → Set _
func A B = A → B

_∘_ : {l : Level} {A B C : Set l} → func B C → func A B → func A C
(g ∘ f) a = g (f a)

open import Relation.Binary.Core -- use _≡_

∘-assoc : ∀{l} {A B C D : Set l} 
               {h : func C D} {g : func B C} {f : func A B}
  → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc = refl

-- P.4
id-func : {l : Level} (A : Set l) → func A A
id-func A = λ a → a

-- "∀{l} = {l : Level}" (syntax sugar)
id-func-right : ∀{l} {A B : Set l} {f : func A B}
 → f ∘ id-func A ≡ f
id-func-right = refl

id-func-left : ∀{l} {A B : Set l} {f : func A B}
 → f ≡ id-func B ∘ f
id-func-left = refl

-------------------------------------
-- 1.3 Definition of a category
-------------------------------------

-- *** Definition 1.1 ***
-- A category consists of the following data:

record Category (c1 c2 l : Level) : Set (suc (c1 ⊔ c2 ⊔ l)) where
  field
    -- data
    Obj  : Set c1 
    Hom  : Obj → Obj → Set c2 
    Comp : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    Id   : (A : Obj) → Hom A A    
    -- equality
    {-
      We should always define equality between any Sets 
        in Constructive type theory.
      so this is truely not a category, but E-category.
    -}
    _≈_ : {A B : Obj} → Hom A B → Hom A B → Set l
    -- axioms for Category
    Id-left : {A B : Obj} {f : Hom A B} → Comp (Id B) f ≈ f
    Id-right : {A B : Obj} {f : Hom A B} → Comp f (Id A) ≈ f
    assoc : {A B C D : Obj} {f : Hom A B} {g : Hom B C} {h : Hom C D}
      → Comp (Comp h g) f ≈ Comp h (Comp g f)
    -- axioms for E-Category
    ≈-refl : {A B : Obj} {x : Hom A B} → x ≈ x
    ≈-sym  : {A B : Obj} {x y : Hom A B} → x ≈ y → y ≈ x
    ≈-trans : {A B : Obj} {x y z : Hom A B} → x ≈ y → y ≈ z → x ≈ z
    Comp-cong : {A B C : Obj} {f f' : Hom A B} {g g' : Hom B C}
      → f ≈ f' → g ≈ g' → Comp g f ≈ Comp g' f' 


sets : {l : Level} → Category _ _ l 
sets {l} = record {
             Obj = Set l;
             Hom = func;
             Comp = _∘_;
             Id = id-func;
             _≈_ = _≡_;
             Id-left = id-func-left;
             Id-right = id-func-right;
             assoc = ∘-assoc;
             ≈-refl = refl;
             ≈-sym = {!!};
             ≈-trans = {!!};
             Comp-cong = {!!} }

