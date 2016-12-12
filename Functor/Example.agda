module Functor.Example where

open import Definition.Functor
open import Category.One renaming (_∘_ to _∘₁_) 
open import Category.Three renaming (_∘_ to _∘₃_) 
open import NotationUtil
import Relation.Binary.PropositionalEquality as Eq

fo13 : Obj[ One ] → Obj[ Three ]
fo13 * = a

fa13 : {x1 x2 : Obj[ One ]} → One [ x1 , x2 ] → Three [ fo13 x1 , fo13 x2 ]
fa13 {*} {*} h = id a

1to3 : One ⟶ Three
1to3 = record
              { fo = fo13;
                fa = fa13;
                id = id-proof ;
                comp = λ {a} {b} {c} {f} {g} → comp-proof {a} {b} {c} {f} {g};
                ≈-resp = resp-proof }
  where
    id-proof : {c : Obj[ One ]} → Three [ fa13 (One [1 c ]) ≈ Three [1 fo13 c ] ]
    id-proof {*} = Eq.refl

    comp-proof : {a b c : Category.Obj One} {f : One [ a , b ]} {g : One [ b , c ]} →
         Three [ fa13 (g ∘₁ f) ≈ fa13 g ∘₃ fa13 f ]
    comp-proof {*} {*} {*} {*→*} {*→*} = Eq.refl

    resp-proof : {a b : Category.Obj One} (f g : One [ a , b ]) →
         One [ f ≈ g ] → Three [ fa13 f ≈ fa13 g ]
    resp-proof {*} {*} *→* *→* Eq.refl = Eq.refl
