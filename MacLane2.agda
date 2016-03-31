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
open import Data.Product renaming (_×_ to _x_)
_×_ : {l1 l2 l3 m1 m2 m3 : Level} → Category l1 l2 l3 → Category m1 m2 m3 → Category {!!} {!!} {!!}
B × C = record
          { Obj = B.Obj x C.Obj
          ; Hom = λ bc b'c' → B.Hom (proj₁ bc) (proj₁ b'c') x C.Hom (proj₂ bc) (proj₂ b'c')
          ; _o_ = λ {bc} {b'c'} {b''c''} fg f'g' → {!!}
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

---------------------------------------
-- 4. Functor Categories
---------------------------------------

-- vertical composition of NT
_∙_ : {l1 l2 l3 m1 m2 m3 : Level} 
      {C : Category l1 l2 l3} {B : Category m1 m2 m3} 
      {R S T : Functor C B} → 
      S ∸> T → R ∸> S → R ∸> T
_∙_ {C = C} {B = B} τ σ = record 
  { func = λ c → B [ τ.func c o σ.func c ] ; 
    commute = λ {c} {c'} {f} → {!!} }
  where
    private module B = Category B
    private module τ = _∸>_ τ
    private module σ = _∸>_ σ

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
