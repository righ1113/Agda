module Curry5 where

open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

postulate
  X Y : Set
  a : {A B : Set} → (A ≡ B) → A
  b : {A B : Set} → (A ≡ B) → B

curry : (X ≡ (X → Y)) → Y
curry p = (b p) (a p)




