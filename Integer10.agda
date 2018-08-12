module Integer10 where

open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl)

-- 整数の素朴な定義
--（succ (succ (pred zero))などが有効、という弱点がある）
data ℤ : Set where
  zero : ℤ
  succ : ℤ → ℤ
  pred : ℤ → ℤ

-- 加法
_+_ : ℤ → ℤ → ℤ
zero + y = y
succ x + zero = succ x
succ x + succ y = succ (succ x + y)
succ x + pred y = x + y
pred x + zero = pred x
pred x + succ y = x + y
pred x + pred y = pred (pred x + y)

-- 反数
opposite : ℤ → ℤ
opposite zero = zero
opposite (succ x) = pred (opposite x)
opposite (pred x) = succ (opposite x)

-- 乗法
_*_ : ℤ → ℤ → ℤ
x * zero = zero
x * succ y = (x * y) + x
x * pred y = (x * y) + (opposite x)

infixl 40 _+_
infixl 60 _*_

-- (-1) * (-1) = (+1)
theorem : pred zero * pred zero ≡ succ zero
theorem = refl
