module Definition.Discrete where
open import Definition.Category

discrete : {l1 l2 l3 : Level} → Category l1 l2 l3 → Set (l1 ⊔ l2)
discrete record { Obj = Obj ; Hom = Hom ; _o_ = _o_ ; Id = Id ;
  assoc = assoc ; unitL = unitL ; unitR = unitR ; ≈-cong = ≈-cong }
  = {a b : Obj} → (f : Hom [ a , b ]')
    → {!!}

