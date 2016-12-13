module Functor.C3toC4 where

open import Definition.Functor
open import Category.Three renaming (_∘_ to _∘₃_)
open import Category.Four  renaming (_∘_ to _∘₄_)
open import NotationUtil
import Relation.Binary.PropositionalEquality as Eq

fo34 : Obj[ Three ] → Obj[ Four ]
fo34 a = o1
fo34 b = o2
fo34 c = o3

fa34 : {x1 x2 : Obj[ Three ]} → Three [ x1 , x2 ] → Four [ fo34 x1 , fo34 x2 ]
fa34 a→b = 1→2
fa34 b→c = 2→3
fa34 a→c = 1→3
fa34 (id a) = id o1
fa34 (id b) = id o2
fa34 (id c) = id o3

3⟶4 : Three ⟶ Four
3⟶4 = record
              { fo = fo34;
                fa = fa34;
                id = id-prf;
                comp = λ {a} {b} {c} {f} {g} → comp-prf {a} {b} {c} {f} {g};
                ≈-resp = resp-prf }
  where
    id-prf : {x : Category.Obj Three} → Four [ fa34 (Three [1 x ]) ≈ Four [1 fo34 x ] ]
    id-prf {a} = Eq.refl
    id-prf {b} = Eq.refl
    id-prf {c} = Eq.refl
    
    comp-prf : {a b c : Category.Obj Three} {f : Three [ a , b ]} {g : Three [ b , c ]} →
               Four [ fa34 (g ∘₃ f) ≈ (fa34 g ∘₄ fa34 f) ]
    comp-prf {f = a→b} {b→c} = Eq.refl
    comp-prf {f = a→b} {id .b} = Eq.refl
    comp-prf {f = b→c} {id .c} = Eq.refl
    comp-prf {f = a→c} {id .c} = Eq.refl
    comp-prf {f = id .a} {a→b} = Eq.refl
    comp-prf {f = id .b} {b→c} = Eq.refl
    comp-prf {f = id .a} {a→c} = Eq.refl
    comp-prf {f = id a} {id .a} = Eq.refl
    comp-prf {f = id b} {id .b} = Eq.refl
    comp-prf {f = id c} {id .c} = Eq.refl 

    resp-prf : {a b : Category.Obj Three} →
               (f g : Three [ a , b ]) → Three [ f ≈ g ] → Four [ fa34 f ≈ fa34 g ]
    resp-prf f .f Eq.refl = Eq.refl
