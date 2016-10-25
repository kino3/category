module Definition.Discrete where
open import Definition.Category

discrete : {l1 l2 l3 : Level} →
  (C : Category l1 l2 l3) →
  (a b : Obj[ C ]) →
  (f : C [ _ , b ]) →
  Set l3
discrete C a b f = (C [ C [1 b ] ≈ f ]) -- all f is equal to Id(b).


