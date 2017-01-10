module Natural.Example where

open import Functor.C3toC4
open import Functor.C3toC4ver2
open import Definition.NaturalTransformation
open import NotationUtil
--open import Definition.Category
open import Definition.Functor renaming (Functor to F)
open import Category.Three
open import Category.Four renaming (_∘_ to _∘₄_)
import Relation.Binary.PropositionalEquality as Eq

nt1-τ : (c : Obj[ Three ]) → Four [ F.fo 3⟶4 c , F.fo 3⟶4' c ]
nt1-τ a = 1→2
nt1-τ b = 2→3
nt1-τ c = 3→4

commute-prf : {c c' : Obj[ Three ]} {f : Three [ c , c' ]} →
              Four [ nt1-τ c' ∘₄ (F.fa 3⟶4 f)
                   ≈ (F.fa 3⟶4' f) ∘₄ (nt1-τ c) ]
commute-prf {a} {a} {id .a} = Eq.refl
commute-prf {a} {b} {a→b}   = Eq.refl
commute-prf {a} {c} {a→c}   = Eq.refl
commute-prf {b} {a} {()}
commute-prf {b} {b} {id .b} = Eq.refl
commute-prf {b} {c} {b→c}   = Eq.refl
commute-prf {c} {a} {()}
commute-prf {c} {b} {()}
commute-prf {c} {c} {id .c} = Eq.refl

nt1 : 3⟶4 ∸> 3⟶4' 
nt1 = record { τ = nt1-τ ;
               commute = λ {c} {c'} {f} → commute-prf  {c} {c'} {f} }


open import Definition.Universal
open import Data.Product

hoge : universal-arrow-from o1 to 3⟶4
hoge = record { r = a ; u = id o1 ;
  prop = universal-prf }
    where
      universal-prf : (d : Obj[ Three ]) (f : Four [ o1 , (F.fo 3⟶4) d ])
        → ∃! (Three [_≈_]) (λ f' → Four [ ((F.fa 3⟶4) f') ∘₄ id o1 ≈ f ])
      universal-prf a (id .o1) = id a , Eq.refl , unique-ida
        where
          unique-ida : {y : Hom3 a a} → Four [ F.fa 3⟶4 y ∘₄ id o1 ≈ id o1 ] → Three [ id a ≈ y ]
          unique-ida {id .a} prf = Eq.refl
      universal-prf b 1→2      = a→b , Eq.refl , unique-a→b
        where
          unique-a→b : {y : Hom3 a b} → Four [ F.fa 3⟶4 y ∘₄ id o1 ≈ 1→2 ] → Three [ a→b ≈ y ]
          unique-a→b {a→b} prf = Eq.refl
      universal-prf c 1→3      = a→c , Eq.refl , unique-a→c
        where
          unique-a→c : {y : Hom3 a c} → Four [ F.fa 3⟶4 y ∘₄ id o1 ≈ 1→3 ] → Three [ a→c ≈ y ]
          unique-a→c {a→c} prf = Eq.refl
