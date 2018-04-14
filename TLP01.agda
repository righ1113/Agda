module TLP01 where

open import Data.Bool
open import Data.Nat
open import Data.String
open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl; sym; cong; cong₂; trans)

_==ℕ_ : ℕ → ℕ → Bool
zero  ==ℕ zero  = true
suc n ==ℕ suc m = n ==ℕ m
_     ==ℕ _     = false

_<ℕ_ : ℕ → ℕ → Bool
_     <ℕ zero  = false
zero  <ℕ suc _ = true
suc n <ℕ suc m = n <ℕ m

-- ----- Star型の定義と同値性 -----
data Star : Set where
  NIL : Star
  TRU : Star
  N   : ℕ → Star
  S   : String → Star
  C   : Star → Star → Star

eqStar : Star → Star → Bool
eqStar NIL NIL = true
eqStar NIL _ = false
eqStar TRU TRU = true
eqStar TRU _ = false
eqStar (N x) (N y) = x ==ℕ y
eqStar (N _) _ = false
eqStar (S x) (S y) = x == y
eqStar (S _) _ = false
eqStar (C x x₁) (C y y₁) = eqStar x y ∧ eqStar x₁ y₁
eqStar (C _ _) _ = false

-- ----- 組込関数の定義 -----
CONS : Star → Star → Star
CONS = C

CAR : Star → Star
CAR (C x _) = x
CAR _ = NIL

CDR : Star → Star
CDR (C _ x₁) = x₁
CDR _ = NIL

ATOM : Star → Star
ATOM (C _ _) = NIL
ATOM _ = TRU

IF : Star → Star → Star → Star
IF TRU a _ = a
IF q a e = if eqStar q NIL then e else a

EQUAL : Star → Star → Star
EQUAL x y = if eqStar x y then TRU else NIL

s-size : Star → ℕ
s-size (C a b) = s-size a + s-size b + 1
s-size _ = 0
SIZE : Star → Star
SIZE x = N (s-size x)

s2n : Star → ℕ
s2n (N x) = x
s2n _ = 0
LT : Star → Star → Star
LT x y = if s2n x <ℕ s2n y then TRU else NIL

-- ----- Starから≡に -----
postulate
  ts : Star → Set
  ~ : Star → Star
  equal-eq : {x y : Star} → ts (EQUAL x y) →  x ≡ y
  ifAP : {q x y : Star} → ts (IF q (EQUAL x y) TRU) → (ts q → x ≡ y)
  ifEP : {q x y : Star} → ts (IF q TRU (EQUAL x y)) → (ts (~ q) → x ≡ y)
-- ----- 公理 -----
  equal-same : (x : Star) → ts (EQUAL x x)
  equal-swap : (x y : Star) → ts (EQUAL (EQUAL x y) (EQUAL y x))
  equal-if : (x y : Star) → ts (IF (EQUAL x y) (EQUAL x y) TRU)
  atom/cons : (x y : Star) → ts (EQUAL (ATOM (CONS x y)) NIL)
  car/cons : (x y : Star) → ts (EQUAL (CAR (CONS x y)) x)
  cdr/cons : (x y : Star) → ts (EQUAL (CDR (CONS x y)) y)
  cons/car+cdr : (x : Star)
    → ts (IF (ATOM x) TRU (EQUAL (CONS (CAR x) (CDR x)) x))
  if-true : (x y : Star) → ts (EQUAL (IF TRU x y) x)
  if-false : (x y : Star) → ts (EQUAL (IF NIL x y) y)
  if-same : (x y : Star) → ts (EQUAL (IF x y y) y)
  if-nest-A : (x y z : Star) → ts (IF x (EQUAL (IF x y z) y) TRU)
  if-nest-E : (x y z : Star) → ts (IF x TRU (EQUAL (IF x y z) z))
  size/car : (x : Star)
    → ts (IF (ATOM x) TRU (EQUAL (LT (SIZE (CAR x)) (SIZE x)) TRU))
  size/cdr : (x : Star)
    → ts (IF (ATOM x) TRU (EQUAL (LT (SIZE (CDR x)) (SIZE x)) TRU))

-- ----- 練習 -----
postulate
  -- a b : Star
  foo : ts (EQUAL TRU NIL)
hoge6 : (a b : Star)
  → (IF (EQUAL TRU NIL) TRU TRU) ≡ (IF (EQUAL TRU NIL) NIL TRU)
hoge6 a b = ifAP (equal-if TRU NIL) foo

hoge2 : (ATOM (CONS TRU TRU)) ≡ NIL
hoge2 = equal-eq (atom/cons TRU TRU)

-- hoge2' : (ATOM (CONS TRU TRU)) ≡ NIL
-- hoge2' rewrite (equal-eq (atom-cons TRU TRU)) = {!!}

hoge3 : (C TRU NIL) ≡ (C TRU NIL)
hoge3 = equal-eq (equal-same (C TRU NIL))

hoge4 : (EQUAL TRU TRU) ≡ TRU
hoge4 = begin
    (if eqStar TRU TRU then TRU else NIL)
  ≡⟨ refl ⟩
    TRU
  ∎
  where open PropEq.≡-Reasoning

hoge5 : (EQUAL NIL NIL) ≡ TRU
hoge5 = refl

postulate
  j : (x : Star) → ts (~ (ATOM x))
hoge7 : (x : ℕ)
  → (IF (ATOM (N x)) TRU (LT (SIZE (CDR (N x))) (SIZE (N x)))) ≡ (IF (ATOM (N x)) TRU TRU)
hoge7 x = ifEP (size/cdr (N x)) (j (N x))
-- -----

{-
-- ----- 停止性で引っかかる -----
memb?' : Star → Star
memb?' xs =
  (IF (ATOM xs)
       NIL
       (IF (EQUAL (CAR xs) (S "?"))
           TRU
           (memb?' (CDR xs))))
-}
-- ----- memb?の停止性 -----
-- ----- SIZEを使う時はℕを引数にとる
postulate
  premise : (xs : Star) → ts (~ (ATOM xs))
measure-memb? : (x : ℕ)
  → (IF (ATOM (N x))
        TRU
        (IF (EQUAL (CAR (N x)) (S "?"))
            TRU
            (LT (SIZE (CDR (N x))) (SIZE (N x)))))
    ≡ TRU
measure-memb? x = begin
    (IF (ATOM (N x))
        TRU
        (IF (EQUAL (CAR (N x)) (S "?"))
            TRU
            (LT (SIZE (CDR (N x))) (SIZE (N x)))))
  ≡⟨ ifEP (size/cdr (N x)) (premise (N x)) ⟩
    (IF (ATOM (N x))
        TRU
        (IF (EQUAL (CAR (N x)) (S "?"))
            TRU
            TRU))
  ≡⟨ equal-eq (if-same (EQUAL (CAR (N x)) (S "?")) TRU) ⟩
    (IF (ATOM (N x))
        TRU
        TRU)
  ≡⟨ equal-eq (if-same (ATOM (N x)) TRU) ⟩
    TRU
  ∎
  where open PropEq.≡-Reasoning

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
-- ----- 帰納的な証明(未完) -----
-- ----- ATOMを使う時はC x yを引数にとる
postulate
  premise2 : (xs : Star) → ts (ATOM xs)
atomt : (ATOM (S "'()")) ≡ TRU
atomt = refl
memb?/remb : (x y : Star)
  → (IF (ATOM (C x y))
        (EQUAL (memb? (remb (C x y))) NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
    ≡      (IF (ATOM (C x y))
        (EQUAL (IF TRU
                    NIL
                    (IF (EQUAL (CAR (S "'()")) (S "?"))
                        TRU
                        (memb? (CDR (S "'()")))))
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
memb?/remb x y = begin
    (IF (ATOM (C x y))
        (EQUAL (memb? (remb (C x y))) NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
  ≡⟨ cong (λ t → ((IF (ATOM (C x y))
        (EQUAL (memb? t) NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU)))) (def-remb (C x y)) ⟩
    (IF (ATOM (C x y))
        (EQUAL (memb? (IF (ATOM (C x y))
          (S "'()")
          (IF (EQUAL (CAR (C x y)) (S "?"))
              (remb (CDR (C x y)))
              (CONS (CAR (C x y))
                 (remb (CDR (C x y)))))))
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
  ≡⟨ ifAP (if-nest-A (ATOM (C x y)) (S "'()") ((IF (EQUAL (CAR (C x y)) (S "?"))
              (remb (CDR (C x y)))
              (CONS (CAR (C x y))
                 (remb (CDR (C x y))))))) (premise2 (C x y)) ⟩
    (IF (ATOM (C x y))
        (EQUAL (memb?
          (S "'()"))
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
  ≡⟨ cong ((λ t → (IF (ATOM (C x y))
        (EQUAL t
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU)))) (def-memb? ((S "'()"))) ⟩
    (IF (ATOM (C x y))
        (EQUAL (IF (ATOM (S "'()"))
                    NIL
                    (IF (EQUAL (CAR (S "'()")) (S "?"))
                        TRU
                        (memb? (CDR (S "'()")))))
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
  ≡⟨ cong ((λ t →     (IF (ATOM (C x y))
        (EQUAL (IF t
                    NIL
                    (IF (EQUAL (CAR (S "'()")) (S "?"))
                        TRU
                        (memb? (CDR (S "'()")))))
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU)))) atomt ⟩
    (IF (ATOM (C x y))
        (EQUAL (IF TRU
                    NIL
                    (IF (EQUAL (CAR (S "'()")) (S "?"))
                        TRU
                        (memb? (CDR (S "'()")))))
                        NIL)
        (IF (EQUAL (memb? (remb (CDR (C x y)))) NIL)
            (EQUAL (memb? (remb (C x y))) NIL)
            TRU))
  ∎
  where open PropEq.≡-Reasoning
