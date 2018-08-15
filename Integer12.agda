module Integer12 where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl; cong; cong₂; sym)


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

postulate -- ここだけ
  ttxS : (x : ℤ) → (isTrue (zeroOrSucc x))
  ttxP : (x : ℤ) → (isTrue (zeroOrPred x))
  succPred :
    (x : ℤ)(px : isTrue (zeroOrPred x))(px2 : isTrue (zeroOrSucc (pred x px)))
      → succ (pred x px) px2 ≡ x
  predSucc :
    (x : ℤ)(px : isTrue (zeroOrSucc x))(px2 : isTrue (zeroOrPred (succ x px)))
      → pred (succ x px) px2 ≡ x
  pxToTtxS : (x : ℤ)(px : isTrue (zeroOrSucc x)) → px ≡ ttxS x
  pyToTtxP : (y : ℤ)(py : isTrue (zeroOrPred y)) → py ≡ ttxP y
  myCong₂S : {x y : ℤ}{u : ⊤}{v : ⊤}
    → x ≡ y → u ≡ v → succ x (ttxS x) ≡ succ y (ttxS y)
  myCong₂P : {x y : ℤ}{u : ⊤}{v : ⊤}
    → x ≡ y → u ≡ v → pred x (ttxP x) ≡ pred y (ttxP y)
  myCong₂ : {A : Set}(x y : A){B : Set}{C : Set}(f : A → B → C){u v : B} →
              x ≡ y → u ≡ v → f x u ≡ f y v

infixl 40 _+_
infixl 60 _*_

-- 加法
_+_ : ℤ → ℤ → ℤ
zero + y = y
succ x px + zero = succ x px
succ x px + succ y py
  = let z = succ x px + y in succ z (ttxS z) 
succ x _ + pred y _ = x + y
pred x px + zero = pred x px
pred x _ + succ y _ = x + y
pred x px + pred y py
  = let z = pred x px + y in pred z (ttxP z) 

-- 反数
opposite : ℤ → ℤ
opposite zero = zero
opposite (succ x px) = pred (opposite x) (ttxP (opposite x))
opposite (pred x px) = succ (opposite x) (ttxS (opposite x))

-- 乗法
_*_ : ℤ → ℤ → ℤ
x * zero = zero
x * succ y py = (x * y) + x
x * pred y py = (x * y) + (opposite x)


-- (-1) * (-1) = 1
-1*-1≡1 : pred zero tt * pred zero tt ≡ succ zero tt
-1*-1≡1 = refl
-- 2 * (-3) = (-6)
2*-3≡-6 :
  succ (succ zero tt) tt * pred (pred (pred zero tt) tt) tt
    ≡ pred (pred (pred (pred (pred (pred zero tt) tt) tt) tt) tt) tt
2*-3≡-6 = refl


-- 雑多な定理
-- 右から0を足しても変わらない
x+zero≡x : (x : ℤ) → x + zero ≡ x
x+zero≡x zero = refl
x+zero≡x (succ _ _) = refl
x+zero≡x (pred _ _) = refl

-- ユーティリティ
mutual
  succOut1 : (x y : ℤ)(px : isTrue (zeroOrSucc x))
    → succ x px + y ≡ succ (x + y) (ttxS (x + y))
  succOut1 x zero px rewrite x+zero≡x x | pxToTtxS x px = refl
  succOut1 x (succ y py) px rewrite succOut1 x y px | succOut2 x y py = refl
  succOut1 x (pred y py) _ rewrite predOut2 x y py
                                 | succPred (x + y) (ttxP (x + y))
      (ttxS (pred (x + y) (ttxP (x + y)))) = refl
  succOut2 : (x y : ℤ)(py : isTrue (zeroOrSucc y))
    → x + succ y py ≡ succ (x + y) (ttxS (x + y))
  succOut2 zero y py rewrite pxToTtxS y py = refl
  succOut2 (succ x px) y py = refl
  succOut2 (pred x px) y py rewrite predOut1 x y px
                                  | succPred (x + y) (ttxP (x + y))
      (ttxS (pred (x + y) (ttxP (x + y)))) = refl
  predOut1 : (x y : ℤ)(px : isTrue (zeroOrPred x))
    → pred x px + y ≡ pred (x + y) (ttxP (x + y))
  predOut1 x zero px rewrite x+zero≡x x | pyToTtxP x px = refl
  predOut1 x (succ y py) px rewrite succOut2 x y py
                                  | predSucc (x + y) (ttxS (x + y))
      (ttxP (succ (x + y) (ttxS (x + y)))) = refl
  predOut1 x (pred y py) px rewrite predOut1 x y px
                                  | predOut2 x y py = refl
  predOut2 : (x y : ℤ)(py : isTrue (zeroOrPred y))
    → x + pred y py ≡ pred (x + y) (ttxP (x + y))
  predOut2 zero y py rewrite pyToTtxP y py = refl
  predOut2 (succ x px) y py rewrite succOut1 x y px
                                  | predSucc (x + y) (ttxS (x + y))
      (ttxP (succ (x + y) (ttxS (x + y)))) = refl
  predOut2 (pred x px) y py = refl

-- 結合法則
ℤ+-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
ℤ+-assoc zero y z = refl
ℤ+-assoc (succ x px) y z rewrite succOut1 x y px
                               | succOut1 (x + y) z (ttxS (x + y))
                               | succOut1 x (y + z) px
                               = myCong₂S (ℤ+-assoc x y z) refl
ℤ+-assoc (pred x px) y z rewrite predOut1 x y px
                               | predOut1 (x + y) z (ttxP (x + y))
                               | predOut1 x (y + z) px
                               = myCong₂P (ℤ+-assoc x y z) refl

-- 左分配法則
ℤdistL : (x y z : ℤ) → x * (y + z) ≡ (x * y) + (x * z)
ℤdistL x y zero rewrite x+zero≡x y | x+zero≡x (x * y) = refl
ℤdistL x y (succ z pz) rewrite succOut2 y z pz
                             | ℤdistL x y z
                             = ℤ+-assoc (x * y) (x * z) x
ℤdistL x y (pred z pz) rewrite predOut2 y z pz
                             | ℤdistL x y z
                             = ℤ+-assoc (x * y) (x * z) (opposite x)

-- oppositeの線形性
oppoLinear : (x y : ℤ) → opposite x + opposite y ≡ opposite (x + y)
oppoLinear x zero rewrite x+zero≡x (opposite x)
                        | x+zero≡x x = refl
oppoLinear x (succ y py) rewrite predOut2 (opposite x) (opposite y) (ttxP (opposite y))
                               | succOut2 x y py
                               = myCong₂P (oppoLinear x y) refl
oppoLinear x (pred y py) rewrite succOut2 (opposite x) (opposite y) (ttxS (opposite y))
                               | predOut2 x y py
                               = myCong₂S (oppoLinear x y) refl













