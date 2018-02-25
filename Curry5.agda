module Curry5 where

open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; subst)
open import Function using (id)

lemma1 : {X Y : Set} → (X ≡ (X → Y)) → X
lemma1 p rewrite p = (λ x → let f = subst id p x in f x)

curry : {X Y : Set} → (X ≡ (X → Y)) → Y
curry p = (let f = subst id p (lemma1 p) in f (lemma1 p))




