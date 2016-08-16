module Category.Sets where

open import Definition.Category
import Relation.Binary.PropositionalEquality as PropEq
import Function.Equality as Feq
import Relation.Binary as B

{-
Agda的な都合でSetoidにしないとダメだが、実態としては本のSetsのように使うので
名前はSetsにする。(正確にはSetoidの圏)
-}
Sets : (c l : Level) → Category (suc (c ⊔ l)) ((c ⊔ l)) ((c ⊔ l))
Sets c l = record
         { Obj = Setoid c l
         ; Hom = Feq._⇨_
         ; _o_ = Feq._∘_
         ; Id  = λ (X : Setoid c l) → Feq.id {c} {l} {X} 
         ; assoc = λ {A B C D f g h} → assoc-proof {A} {B} {C} {D} {f} {g} {h}
         ; unitL = λ {A B f} → unitL-proof {A} {B} {f}
         ; unitR = λ {B C g} → Feq.cong g
         ; ≈-cong = λ {A} {B} {C} {f1} {f2} {g1} {g2} →
                    λ f1≈f2 g1≈g2 x≈y → g1≈g2 (f1≈f2 x≈y)
         }
   where
     -- 冗長だが、思い出し用に残す
     assoc-proof : {A B C D : Setoid c l}  {f : Feq._⇨_ [ A , B ]'}
                  {g : Feq._⇨_ [ B , C ]'} {h : Feq._⇨_ [ C , D ]'}
                  {x y : Setoid.Carrier A} →
      (A Setoid.≈ x) y →
      (D Setoid.≈ h Feq.⟨$⟩ (g Feq.⟨$⟩ (f Feq.⟨$⟩ x)))
      (h Feq.⟨$⟩ (g Feq.⟨$⟩ (f Feq.⟨$⟩ y)))
     assoc-proof {A} {B} {C} {D} {f} {g} {h} = Feq.cong (h Feq.∘ g Feq.∘ f)

     unitL-proof : {A B : Setoid c l} {f : Feq._⇨_ [ A , B ]'}
      {x y : Setoid.Carrier A} →
      (A Setoid.≈ x) y → (B Setoid.≈ f Feq.⟨$⟩ x) (f Feq.⟨$⟩ y)
     unitL-proof {A} {B} {f} {x} {y} = Feq.cong f

