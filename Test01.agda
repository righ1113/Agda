module Test01 where

hoge : {A : Set} → A → A
hoge x = x

open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; subst)
open import Function using (id)

lemma1 : {X Y : Set} → (X ≡ (X → Y)) → X
lemma1 p rewrite p = (λ x → let f = subst id p x in f x)

curry : {X Y : Set} → (X ≡ (X → Y)) → Y
curry p = (let f = subst id p (lemma1 p) in f (lemma1 p))

open import Data.Bool
open import Data.Nat
open import Data.Empty

postulate
  First : ℕ → Set
  All   : ℕ → Set
  fToA  : ((n : ℕ) → First n) → ((n : ℕ) → All n)
  fToA2 : (z : ℕ) → (First z → All z)
  tekito : (z : ℕ) → ((All z → ⊥) → (First z → ⊥)) → First (suc z)
  contra : (z : ℕ) → ((All z → ⊥) → (First z → ⊥)) → (First z → All z)

mutual
  -- 失敗
  contraFirstToAll : (z : ℕ) → ((All z → ⊥) → (First z → ⊥))
  -- contraFirstToAll z allToVoid _ = let foo = (contra z (contraFirstToAll z)) (limitedDivSeq z) in  allToVoid foo
  contraFirstToAll z allToVoid _ = let foo = fToA (λ k → limitedDivSeq k) in  allToVoid (foo z)

  limitedDivSeq : (n : ℕ) → First n
  limitedDivSeq zero    = {!   !}
  limitedDivSeq (suc n) = let bar = contraFirstToAll n in tekito n bar