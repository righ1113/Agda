module Integer12 where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_;  _∘′_)
open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl; cong; sym)


isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

-- 整数のガチな定義
--（succ (succ (pred zero))などはもうできない）
mutual
  data ℤ : Set where
    zero : ℤ
    succ : (x : ℤ) → isTrue (zeroOrSucc x) → ℤ
    pred : (x : ℤ) → isTrue (zeroOrPred x) → ℤ

  zeroOrSucc : ℤ → Bool
  zeroOrSucc zero = true
  zeroOrSucc (succ x p) = true
  zeroOrSucc (pred x p) = false
  zeroOrPred : ℤ → Bool
  zeroOrPred zero = true
  zeroOrPred (succ x p) = false
  zeroOrPred (pred x p) = true
-- succ (succ zero tt) tt のように使う

-- 加法
mutual
  _+_ : ℤ → ℤ → ℤ
  zero + y = y
  succ x px + zero = succ x px
  succ x px + succ y py
    = let z = succ x px + y in succ z (tt₂ x y px py) 
  succ x _ + pred y _ = x + y
  pred x px + zero = pred x px
  pred x _ + succ y _ = x + y
  pred x px + pred y py
    = let z = pred x px + y in pred z (tt₃ x y px py) 
  postulate
    tt₂ : (x y : ℤ) → (px : isTrue (zeroOrSucc x))
                        → (py : isTrue (zeroOrSucc y))
      →  isTrue (zeroOrSucc (succ x px + y))
    tt₃ : (x y : ℤ) → (px : isTrue (zeroOrPred x))
                        → (py : isTrue (zeroOrPred y))
      →  isTrue (zeroOrPred (pred x px + y))

-- 反数
mutual
  opposite : ℤ → ℤ
  opposite zero = zero
  opposite (succ x px) = pred (opposite x) (tt₄ x px)
  opposite (pred x px) = succ (opposite x) (tt₅ x px)
  postulate
     tt₄ : (x : ℤ) → (px : isTrue (zeroOrSucc x))
       → isTrue (zeroOrPred (opposite x))
     tt₅ : (x : ℤ) → (px : isTrue (zeroOrPred x))
       → isTrue (zeroOrSucc (opposite x))

-- 乗法
_*_ : ℤ → ℤ → ℤ
x * zero = zero
x * succ y py = (x * y) + x
x * pred y py = (x * y) + (opposite x)

infixl 40 _+_
infixl 60 _*_

-- (-1) * (-1) = (+1) その1
theorem1 : pred zero tt * pred zero tt ≡ succ zero tt
theorem1 = refl

-- (-1) * (-1) = (+1) その2
-- 「反数の反数」を使ってはいけないらしい
-- (-1) * 0 ≡ (-1) * (-1) + (-1)
-- rewrite x * 0 ≡ 0
-- x ≡ y → x + 1 ≡ y + 1
-- rewrite 0 + 1 ≡ 1
-- 結合法則 rewrite (x + y) + z ≡ x + (y + z)
-- rewrite (-1) + 1 ≡ 0
-- rewrite x + 0 ≡ x
-- 左辺と右辺を入れ替える
-₁ = pred zero tt
one = succ zero tt

seed : -₁ * zero ≡ -₁ * -₁ + -₁
seed = refl
lemma1 : (-₁ * zero ≡ -₁ * -₁ + -₁) → (zero ≡ -₁ * -₁ + -₁)
lemma1 _ = refl
lemma2 : (zero ≡ -₁ * -₁ + -₁) → (zero + one ≡ -₁ * -₁ + -₁ + one)
lemma2 p = cong (_+ one) p
lemma3 : (zero + one ≡ -₁ * -₁ + -₁ + one) → (one ≡ -₁ * -₁)
lemma3 _ = refl
lemma4 : (one ≡ -₁ * -₁) → (-₁ * -₁ ≡ one)
lemma4 p = sym p

theorem2 : pred zero tt * pred zero tt ≡ succ zero tt
theorem2 = lemma4 (lemma3 (lemma2 (lemma1 seed)))




