module MacLane2 where
{-
 II. Constructions on Categories
-}
open import MacLane1

---------------------------------------
-- 1. Duality
---------------------------------------

---------------------------------------
-- 2. Contravariance and Opposites
---------------------------------------

---------------------------------------
-- 3. Products of Categories
---------------------------------------
{-
open import Data.Product
_×c_ : {l1 l2 l3 m1 m2 m3 : Level} → Category l1 l2 l3 → Category m1 m2 m3 → Category {!!} {!!} {!!}
B ×c C = record
          { Obj = B.Obj × C.Obj
          ; Hom = λ x y → B.Hom (proj₁ x) (proj₁ y) × C.Hom (proj₂ x) (proj₂ y)
          ; _o_ = {!!}
          ; id = {!!}
          ; _≈_ = {!!}
          ; assoc = {!!}
          ; unitL = {!!}
          ; unitR = {!!}
          ; ≈-equiv = {!!}
          ; ≈-cong = {!!}
          }
 where
   private module B = Category B
   private module C = Category C
-}
---------------------------------------
-- 4. Functor Categories
---------------------------------------

-- vertical composition of NT
_∙_ : {l1 l2 l3 m1 m2 m3 : Level} 
      {C : Category l1 l2 l3} {B : Category m1 m2 m3} 
      {R S T : Functor C B} → 
      S ∸> T → R ∸> S → R ∸> T
_∙_ {C = C} {B = B} τ σ = record 
  { τ = λ c → B [ (_∸>_.τ τ c) o _∸>_.τ σ c ] ; 
    prop = {!!} }
  where
    private module B = Category B
    private module τ = _∸>_ τ
---------------------------------------
-- 5. The Category of All Categories
---------------------------------------

---------------------------------------
-- 6. Comma Categories
---------------------------------------
{-
CommaCat : {l1 l2 l3 m1 m2 m3 : Level} → Category l1 l2 l3 → Category {!!} m2 m3
CommaCat C = record
               { Obj = {!!} --Σ[ c ∈ C.Obj ] C.Hom _ c
               ; Hom = {!!}
               ; _o_ = {!!}
               ; id = {!!}
               ; _≈_ = {!!}
               ; assoc = {!!}
               ; unitL = {!!}
               ; unitR = {!!}
               ; ≈-equiv = {!!}
               ; ≈-cong = {!!}
               }
  where
    private module C = Category C
-}
