module ZisRing where

open import Data.Product using (_×_; _,_) 
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  as PropEq using (_≡_; refl; cong; sym)

open import Integer10 -- 整数の定義

-- ---------- record ----------
record IsSemiGroup (A : Set) (_∙_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
record IsMonoid (A : Set) (_∙_ : A → A → A) (e : A) : Set where
  field
    isSemiGroup : IsSemiGroup A _∙_
    identity : (∀ x → e ∙ x ≡ x) × (∀ x → x ∙ e ≡ x)
record IsGroup (A : Set) (_∙_ : A → A → A) (e : A) (iF : A → A) : Set where
  field
    isMonoid : IsMonoid A _∙_ e
    inv : (∀ x → (iF x) ∙ x ≡ e) × (∀ x → x ∙ (iF x) ≡ e)
record IsAbelianGroup (A : Set) (_∙_ : A → A → A) (e : A) (iF : A → A) : Set where
  field
    isGroup : IsGroup A _∙_ e iF
    comm : ∀ x y → x ∙ y ≡ y ∙ x
record IsRing (A : Set) (_⊕_ _⊗_ : A → A → A) (eP eT : A) (iF : A → A) : Set where
  field
    ⊕isAbelianGroup : IsAbelianGroup A _⊕_ eP iF
    ⊗isMonoid : IsMonoid A _⊗_ eT
    isDistR : (x y z : A) → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)
    isDistL : (x y z : A) → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)
-- ----------------------------

-- Z,+が半群であること
lemma5 : (x : ℤ) → x + zero ≡ x
lemma5 zero = refl
lemma5 (succ _) = refl
lemma5 (pred _) = refl
postulate
  succPred : (x : ℤ) → succ (pred x) ≡ x
  predSucc : (x : ℤ) → pred (succ x) ≡ x
mutual
  succOut1 : (x y : ℤ) → succ x + y ≡ succ (x + y)
  succOut1 x zero = cong succ (sym (lemma5 x))
  succOut1 x (succ y) rewrite succOut1 x y
                                            | succOut2 x y = refl
  succOut1 x (pred y) rewrite predOut2 x y
                                            | succPred (x + y) = refl
  succOut2 : (x y : ℤ) → x + succ y ≡ succ (x + y)
  succOut2 zero y = refl
  succOut2 (succ x) y = refl
  succOut2 (pred x) y rewrite predOut1 x y
                                            | succPred (x + y) = refl
  predOut1 : (x y : ℤ) → pred x + y ≡ pred (x + y)
  predOut1 x zero = cong pred (sym (lemma5 x))
  predOut1 x (succ y) rewrite succOut2 x y
                                            | predSucc (x + y) = refl
  predOut1 x (pred y) rewrite predOut1 x y
                                            | predOut2 x y = refl
  predOut2 : (x y : ℤ) → x + pred y ≡ pred (x + y)
  predOut2 zero y = refl
  predOut2 (succ x) y rewrite succOut1 x y
                                            | predSucc (x + y) = refl
  predOut2 (pred x) y = refl

ℤ+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
ℤ+-assoc zero y z = refl
ℤ+-assoc (succ x) zero z = refl
ℤ+-assoc (succ x) (succ y) zero = refl
ℤ+-assoc (succ x) (succ y) (succ z) = lemma6 x y z
  where
    lemma6 : (x y z : ℤ) →
      succ (succ (succ x + y) + z) ≡ succ (succ x + (succ y + z))
    lemma6 x y z rewrite succOut1 x y
                                    | succOut1 (succ (x + y)) z
                                    | succOut1 (x + y) z
                                    | succOut1 x (succ y + z)
                                    | succOut1 y z
                                    | succOut2 x (y + z)
            = cong (λ x → succ (succ (succ x))) (ℤ+-assoc x y z)
ℤ+-assoc (succ x) (succ y) (pred z) = ℤ+-assoc (succ x) y z
ℤ+-assoc (succ x) (pred y) zero = lemma5 (x + y)
ℤ+-assoc (succ x) (pred y) (succ z) rewrite succOut2 (x + y) z
                                                                  | succOut1 x (y + z)
            = cong succ (ℤ+-assoc x y z)
ℤ+-assoc (succ x) (pred y) (pred z) rewrite predOut2 (x + y) z
                                                                  | predOut1 y z
                                                                  | predOut2 x (y + z)
            = cong pred (ℤ+-assoc x y z)
ℤ+-assoc (pred x) zero z = refl
ℤ+-assoc (pred x) (succ y) zero = lemma5 (x + y)
ℤ+-assoc (pred x) (succ y) (succ z) rewrite succOut2 (x + y) z
                                                                  | succOut1 y z
                                                                  | succOut2 x (y + z)
            = cong succ (ℤ+-assoc x y z) 
ℤ+-assoc (pred x) (succ y) (pred z) rewrite predOut2 (x + y) z
                                                                  | predOut1 x (y + z)
            = cong pred (ℤ+-assoc x y z)
ℤ+-assoc (pred x) (pred y) zero = refl
ℤ+-assoc (pred x) (pred y) (succ z) = ℤ+-assoc (pred x) y z
ℤ+-assoc (pred x) (pred y) (pred z) rewrite predOut1 (pred x + y) z
                                                                  | predOut1 x y
                                                                  | predOut1 (x + y) z
                                                                  | predOut1 x (pred y + z)
                                                                  | predOut1 y z
                                                                  | predOut2 x (y + z)
            = cong (λ x → pred (pred (pred x))) (ℤ+-assoc x y z)
ℤ+-isSemiGroup : IsSemiGroup ℤ _+_
ℤ+-isSemiGroup = record { assoc = ℤ+-assoc }

-- Z,+がモノイドであること
ℤ+Zero-isMonoid : IsMonoid ℤ _+_ zero
ℤ+Zero-isMonoid = record { isSemiGroup = ℤ+-isSemiGroup ;
                                              identity = (zero+x≡x , x+zero≡x) }
  where
    zero+x≡x : ∀ x → zero + x ≡ x
    zero+x≡x _ = refl
    x+zero≡x : ∀ x → x + zero ≡ x
    x+zero≡x = lemma5

-- Z,+が群であること
leftInv : ∀ x → (opposite x + x) ≡ zero
leftInv zero = refl
leftInv (succ x) = leftInv x
leftInv (pred x) = leftInv x
rightInv : ∀ x → (x + opposite x) ≡ zero
rightInv zero = refl
rightInv (succ x) = rightInv x
rightInv (pred x) = rightInv x
ℤ+ZeroOpposite-isGroup : IsGroup ℤ _+_ zero opposite
ℤ+ZeroOpposite-isGroup = record { isMonoid = ℤ+Zero-isMonoid ;
                                                           inv = (leftInv , rightInv) }

-- Z,+がアーベル群であること
ℤ+ZeroOpposite-Comm : ∀ x y → (x + y) ≡ (y + x)
ℤ+ZeroOpposite-Comm zero y = sym (lemma5 y)
ℤ+ZeroOpposite-Comm (succ x) y rewrite succOut1 x y
                                                                 | succOut2 y x
          = cong succ (ℤ+ZeroOpposite-Comm x y)
ℤ+ZeroOpposite-Comm (pred x) y rewrite predOut1 x y
                                                                 | predOut2 y x
          = cong pred (ℤ+ZeroOpposite-Comm x y)
ℤ+ZeroOpposite-isAbelianGroup : IsAbelianGroup ℤ _+_ zero opposite
ℤ+ZeroOpposite-isAbelianGroup
  = record { isGroup = ℤ+ZeroOpposite-isGroup ;
                    comm = ℤ+ZeroOpposite-Comm }


-- Z,*が半群であること
lemma7 : (x y z : ℤ) → x * (y + z) ≡ (x * y) + (x * z)
lemma7 x y zero rewrite lemma5 y | lemma5 (x * y) = refl
lemma7 x y (succ z) rewrite succOut2 y z | lemma7 x y z
  = ℤ+-assoc (x * y) (x * z) x
lemma7 x y (pred z) rewrite predOut2 y z | lemma7 x y z
  = ℤ+-assoc (x * y) (x * z) (opposite x)
postulate lemma8 : (x y : ℤ) → x * opposite y ≡ opposite (x * y)
ℤ*-isSemiGroup : IsSemiGroup ℤ _*_
ℤ*-isSemiGroup = record { assoc = ℤ*-assoc }
  where
    ℤ*-assoc : ∀ x y z → ((x * y) * z) ≡ (x * (y * z))
    ℤ*-assoc x y zero = refl
    ℤ*-assoc x y (succ z) rewrite lemma7 x (y * z) y
      = cong (_+ (x * y)) (ℤ*-assoc x y z)
    ℤ*-assoc x y (pred z) rewrite lemma7 x (y * z) (opposite y)
                                                | lemma8 x y
      = cong (_+ opposite (x * y)) (ℤ*-assoc x y z)

-- Z,*がモノイドであること
one = succ zero
ℤ*One-isMonoid : IsMonoid ℤ _*_ one
ℤ*One-isMonoid = record { isSemiGroup = ℤ*-isSemiGroup ;
                                              identity = (one*x≡x , x*one≡x) }
  where
    one*x≡x : ∀ x → (succ zero) * x ≡ x
    one*x≡x zero = refl
    one*x≡x (succ x) rewrite succOut2 (succ zero * x) zero
                                          | lemma5 (succ zero * x) = cong succ (one*x≡x x)
    one*x≡x (pred x) rewrite predOut2 (succ zero * x) zero
                                          | lemma5 (succ zero * x) = cong pred (one*x≡x x)
    x*one≡x : ∀ x → x * one ≡ x
    x*one≡x _ = refl


-- Z,が環であること
ℤ+ZeroOppo-*One-isRing : IsRing ℤ _+_ _*_ zero one opposite
ℤ+ZeroOppo-*One-isRing
  = record { ⊕isAbelianGroup = ℤ+ZeroOpposite-isAbelianGroup ;
                    ⊗isMonoid = ℤ*One-isMonoid ;
                    isDistR = isDistR-Z ;
                    isDistL = lemma7 }
    where
      lemma9 : ∀ a b c d → ((a + b) + (c + d)) ≡ ((a + c) + (b + d))
      lemma9 zero b c d rewrite sym (ℤ+-assoc b c d)
                                               | ℤ+ZeroOpposite-Comm b c
         = ℤ+-assoc c b d
      lemma9 (succ a) b c d rewrite succOut1 a b
                                              | succOut1 (a + b) (c + d)
                                              | succOut1 a c
                                              | succOut1 (a + c) (b + d)
         = cong succ (lemma9 a b c d)
      lemma9 (pred a) b c d  rewrite predOut1 a b
                                              | predOut1 (a + b) (c + d)
                                              | predOut1 a c
                                              | predOut1 (a + c) (b + d)
         = cong pred (lemma9 a b c d)
      postulate lemma10 : ∀ x y → opposite (x + y) ≡ opposite x + opposite y 
      isDistR-Z : ∀ x y z → ((x + y) * z) ≡ ((x * z) + (y * z))
      isDistR-Z x y zero = refl
      isDistR-Z x y (succ z) rewrite isDistR-Z x y z = lemma9 (x * z) (y * z) x y
      isDistR-Z x y (pred z) rewrite lemma10 x y | isDistR-Z x y z
        = lemma9 (x * z) (y * z) (opposite x) (opposite y)


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
-₁ = pred zero

seed2 : (x : ℤ) → x * zero ≡ x * -₁ + x
seed2 x rewrite leftInv x = refl
lemma1 : (-₁ * zero ≡ -₁ * -₁ + -₁) → (zero ≡ -₁ * -₁ + -₁)
lemma1 prf = prf
lemma2 : (zero ≡ -₁ * -₁ + -₁) → (zero + one ≡ -₁ * -₁ + -₁ + one)
lemma2 prf = cong (_+ one) prf
lemma3 : (zero + one ≡ -₁ * -₁ + -₁ + one) → (one ≡ -₁ * -₁)
lemma3 prf = prf
lemma4 : (one ≡ -₁ * -₁) → (-₁ * -₁ ≡ one)
lemma4 p = sym p

theorem2 : pred zero * pred zero ≡ succ zero
theorem2 = (lemma4 ∘ lemma3 ∘ lemma2 ∘ lemma1) (seed2 -₁)








