module TLP02 where

open import Data.Bool
open import Data.Nat
open import Data.String
open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl)

-- ----- Star型の定義 -----
data Star : Set where
  NIL : Star
  TRU : Star
  N   : ℕ → Star
  S   : String → Star
  C   : Star → Star → Star

-- ----- 組込関数の定義 -----
postulate
  CONS : Star → Star → Star
  CAR : Star → Star
  CDR : Star → Star
  ATOM : Star → Star
  IF : Star → Star → Star → Star
  EQUAL : Star → Star → Star
  SIZE : Star → Star
  LT : Star → Star → Star

-- ----- Starから≡に -----
postulate
  ~ : Star → Star
  equal-eq : {x y : Star} → (EQUAL x y) ≡ TRU →  x ≡ y
  ifAP : {q x y : Star} → (IF q (EQUAL x y) TRU) ≡ TRU → (q ≡ TRU → x ≡ y)
  ifEP : {q x y : Star} → (IF q TRU (EQUAL x y)) ≡ TRU → ((~ q) ≡ TRU → x ≡ y)
-- ----- 公理 -----
  equal-same : (x : Star) → (EQUAL (EQUAL x x) TRU) ≡ TRU
  equal-swap : (x y : Star) → (EQUAL (EQUAL x y) (EQUAL y x)) ≡ TRU
  equal-if : (x y : Star) → (IF (EQUAL x y) (EQUAL x y) TRU) ≡ TRU
  atom/cons : (x y : Star) → (EQUAL (ATOM (CONS x y)) NIL) ≡ TRU
  car/cons : (x y : Star) → (EQUAL (CAR (CONS x y)) x) ≡ TRU
  cdr/cons : (x y : Star) → (EQUAL (CDR (CONS x y)) y) ≡ TRU
  cons/car+cdr : (x : Star)
    → (IF (ATOM x) TRU (EQUAL (CONS (CAR x) (CDR x)) x)) ≡ TRU
  if-true : (x y : Star) → (EQUAL (IF TRU x y) x) ≡ TRU
  if-false : (x y : Star) → (EQUAL (IF NIL x y) y) ≡ TRU
  if-same : (x y : Star) → (EQUAL (IF x y y) y) ≡ TRU
  if-nest-A : (x y z : Star) → (IF x (EQUAL (IF x y z) y) TRU) ≡ TRU
  if-nest-E : (x y z : Star) → (IF x TRU (EQUAL (IF x y z) z)) ≡ TRU
  size/car : (x : Star)
    → (IF (ATOM x) TRU (EQUAL (LT (SIZE (CAR x)) (SIZE x)) TRU)) ≡ TRU
  size/cdr : (x : Star)
    → (IF (ATOM x) TRU (EQUAL (LT (SIZE (CDR x)) (SIZE x)) TRU)) ≡ TRU

-- ----- 練習 -----
hoge2 : (ATOM (CONS TRU TRU)) ≡ NIL
hoge2 = equal-eq (atom/cons TRU TRU)

hoge2' : (ATOM (CONS TRU TRU)) ≡ NIL
hoge2'
  rewrite (equal-eq (atom/cons TRU TRU))
    = refl
-- -----

{--
-- ----- 停止性で引っかかる -----
memb?' : Star → Star
memb?' xs =
  (IF (ATOM xs)
       NIL
       (IF (EQUAL (CAR xs) (S "?"))
           TRU
           (memb?' (CDR xs))))
--}
-- ----- memb?の停止性 -----
postulate
  premise : (xs : Star) → (~ (ATOM xs)) ≡ TRU
measure-memb? : (xs : Star)
  → (IF (ATOM xs)
        TRU
        (IF (EQUAL (CAR xs) (S "?"))
            TRU
            (LT (SIZE (CDR xs)) (SIZE xs))))
    ≡ TRU
measure-memb? xs
  rewrite (ifEP (size/cdr xs) (premise xs))
        | (equal-eq (if-same (EQUAL (CAR xs) (S "?")) TRU))
        | (equal-eq (if-same (ATOM xs) TRU)) = refl

-- ----- memb?の定義 -----
postulate
  memb? : Star → Star
  def-memb? : (xs : Star) →
    memb? xs ≡
      (IF (ATOM xs)
          NIL
          (IF (EQUAL (CAR xs) (S "?"))
              TRU
              (memb? (CDR xs))))
-- ----- rembの定義 -----
postulate
  remb : Star → Star
  def-remb : (xs : Star) →
    remb xs ≡
      (IF (ATOM xs)
          (S "'()")
          (IF (EQUAL (CAR xs) (S "?"))
              (remb (CDR xs))
              (CONS (CAR xs)
                 (remb (CDR xs)))))
-- ----- 帰納的な証明 -----
postulate
  premise2 : (xs : Star) → (ATOM xs) ≡ TRU
  premise3 : (xs : Star) → ~ (ATOM xs) ≡ TRU
  atomt : (ATOM (S "'()")) ≡ TRU
memb?/remb : (xs : Star)
  → (IF (ATOM xs)
        (EQUAL (memb? (remb xs)) NIL)
        (IF (EQUAL (memb? (remb (CDR xs))) NIL)
            (EQUAL (memb? (remb xs)) NIL)
            TRU))
    ≡ IF (ATOM xs) TRU (IF (EQUAL (memb? (remb (CDR xs))) NIL) TRU TRU)
memb?/remb xs
  rewrite (def-remb xs)
        | (ifAP (if-nest-A (ATOM xs) (S "'()") ((IF (EQUAL (CAR xs) (S "?"))
              (remb (CDR xs))
              (CONS (CAR xs)
                 (remb (CDR xs)))))) (premise2 xs))
        | (def-memb? ((S "'()")))
        | (atomt)
        | (equal-eq (if-true NIL ((IF (EQUAL (CAR (S "'()")) (S "?"))
                        TRU
                        (memb? (CDR (S "'()")))))))
        | (equal-eq (equal-same NIL))
        | (def-remb xs)
          -- ----- ここで証明ステップが一気に進んだ
        | (ifEP (if-nest-E (ATOM xs) (S "'()") (IF (EQUAL (CAR xs) (S "?"))
              (remb (CDR xs))
              (CONS (CAR xs)
                 (remb (CDR xs))))) (premise3 xs)) = refl

memb?/remb2 : (xs : Star)
  → IF (ATOM xs) TRU (IF (EQUAL (memb? (remb (CDR xs))) NIL) TRU TRU)
    ≡ TRU
memb?/remb2 xs
  rewrite (equal-eq (if-same (EQUAL (memb? (remb (CDR xs))) NIL) TRU))
        | (equal-eq (if-same (ATOM xs) TRU)) = refl

