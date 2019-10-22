module ColDivSeq where


open import Data.Nat using (ℕ; zero; suc)


-- -----------------------------------------------
data OneCounter : Set where
  ZeroCounter : OneCounter

data LTOneCounter : ℕ → Set where
  Is : (ℕ → LTOneCounter 0) → OneCounter → LTOneCounter 0

data CollatzIsTrue : Set where
  -- 再帰する時に引数を減らしたから、こっちも減らすべき？
  -- いやちがうな
  Is : (LTOneCounter 0) → CollatzIsTrue

data Hoge : Set where
  Is : CollatzIsTrue → Hoge

-- 1x+1&3x+1DoNotHave2Counter : ℕ → (m : ℕ) → n:ℕ → (Hoge) →「R(m)=1かつR(n)=1かつm≠nかつR(m)≠R(n)」🔴
-- 　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　　↑ m, nは存在量化する
1x+1&3x+1isLT1Counter : ℕ → (m : ℕ) → ℕ → (Hoge) → LTOneCounter m
1x+1&3x+1isLT1Counter d m n = {!!}


fToA : ℕ → Hoge
-- ↓CollatzIsTrueにdがあらわれてないと、
-- 1x+1と3x+1のどちらを証明したか分からない
final : ℕ → CollatzIsTrue
fToA d = Is (final d)
final zero = {!!}
final (suc d) = Is (1x+1&3x+1isLT1Counter 1 0 2 (fToA d))




