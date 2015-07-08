module Group where

open import Algebra
open import Data.Integer
open import Relation.Binary.Core using (_≡_;refl)
open import Data.Nat using (zero)
open import Data.Product
open import Level renaming (zero to lzero)

Zsym : {i j : ℤ} → i ≡ j → j ≡ i
Zsym {i} {.i} refl = refl

Ztrans : {i j k : ℤ} → i ≡ j → j ≡ k → i ≡ k
Ztrans {i} {.i} {.i} refl refl = refl

Zassoc : {i j k : ℤ} → (i + j) + k ≡ i + (j + k)
Zassoc { -[1+ n ]} = {!!}
Zassoc {+ zero} {j} {k} = {!!}
Zassoc {+ Data.Nat.suc n} = {!!}

hoge : Group lzero lzero
hoge = record
         { Carrier = ℤ ; 
           _≈_ = _≡_ ; 
           _∙_ = _+_ ; 
           ε = + zero ;
           _⁻¹ = λ z → - z ; 
           isGroup = record { isMonoid = 
                                record { isSemigroup = record { isEquivalence = record { refl = refl ; sym = Zsym ; trans = Ztrans } ; 
                                                                assoc = {!!} ; 
                                                                ∙-cong = {!!} } ; 
                                         identity = {!!} , {!!} } ; 
                              inverse = {!!} , {!!} ; 
                              ⁻¹-cong = λ i≡j → {!!} } }


record Jundokei {l1 l2} (a a' : Group l1 l2) : Set where
