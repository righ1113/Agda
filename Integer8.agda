module Integer8 where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq

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

-- ---------- practice nat ----------
ℕ+-isSemiGroup : IsSemiGroup ℕ _+_
ℕ+-isSemiGroup = record { assoc = ℕ+-assoc }
  where
    ℕ+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    ℕ+-assoc zero y z = refl
    ℕ+-assoc (suc x) y z = cong suc (ℕ+-assoc x y z)

ℕ+0-isMonoid : IsMonoid ℕ _+_ 0
ℕ+0-isMonoid = record { isSemiGroup = ℕ+-isSemiGroup ; identity = (0+x≡x , x+0≡x) }
  where
    0+x≡x : ∀ x → 0 + x ≡ x
    0+x≡x x = refl
    x+0≡x : ∀ x → x + 0 ≡ x
    x+0≡x zero = refl
    x+0≡x (suc x) = cong suc (x+0≡x x)
-- -------------------------

-- ---------- Int ----------
data ℤ : Set where
  O : ℤ
  I : ℕ → ℕ → ℤ
postulate
  zeroZ : (x : ℕ) → I x x ≡ O
  zeroZ₂ : (x y : ℕ) → I (x + y) (y + x) ≡ O
-- plusInt
_++_ : ℤ → ℤ → ℤ
O ++ O = O
O ++ X = X
X ++ O = X
I x y ++ I z w = I (x + z) (y + w)
-- productInt
_**_ : ℤ → ℤ → ℤ
O ** O = O
O ** _ = O
_ ** O = O
I x y ** I z w = I (x * z + y * w) (x * w + y * z)
-- -------------------------

-- ---------- Int + ----------
ℤ++-isSemiGroup : IsSemiGroup ℤ _++_
ℤ++-isSemiGroup = record { assoc = ℤ++-assoc }
  where
    open IsSemiGroup
    ℤ++-assoc : ∀ x y z → (x ++ y) ++ z ≡ x ++ (y ++ z)
    ℤ++-assoc O O O = refl
    ℤ++-assoc O O (I x x₁) = refl
    ℤ++-assoc O (I x x₁) O = refl
    ℤ++-assoc O (I x x₁) (I x₂ x₃) = refl
    ℤ++-assoc (I x x₁) O O = refl
    ℤ++-assoc (I x x₁) O (I x₂ x₃) = refl
    ℤ++-assoc (I x x₁) (I x₂ x₃) O = refl
    ℤ++-assoc (I x x₁) (I x₂ x₃) (I x₄ x₅)
      = cong₂ I ((assoc ℕ+-isSemiGroup) x x₂ x₄) ((assoc ℕ+-isSemiGroup) x₁ x₃ x₅)

ℤ++O-isMonoid : IsMonoid ℤ _++_ O
ℤ++O-isMonoid = record { isSemiGroup = ℤ++-isSemiGroup ; identity = (O++x≡x , x++O≡x) }
  where
    O++x≡x : (x : ℤ) → (O ++ x) ≡ x
    O++x≡x O = refl
    O++x≡x (I x x₁) = refl
    x++O≡x : (x : ℤ) → (x ++ O) ≡ x
    x++O≡x O = refl
    x++O≡x (I x x₁) = refl

invℤ : ℤ → ℤ
invℤ O = O
invℤ (I x x₁) = I x₁ x
ℤ++Oinvℤ-isGroup : IsGroup ℤ _++_ O invℤ
ℤ++Oinvℤ-isGroup = record { isMonoid = ℤ++O-isMonoid ; inv = (leftInv , rightInv) }
  where
    leftInv : (x : ℤ) → (invℤ x ++ x) ≡ O
    leftInv O = refl
    leftInv (I x x₁) = zeroZ₂ x₁ x
    rightInv : (x : ℤ) → (x ++ invℤ x) ≡ O
    rightInv O = refl
    rightInv (I x x₁) = zeroZ₂ x x₁

ℤ++Oinvℤ-isAbelianGroup : IsAbelianGroup ℤ _++_ O invℤ
ℤ++Oinvℤ-isAbelianGroup = record { isGroup = ℤ++Oinvℤ-isGroup ; comm = ℤ++Oinvℤ-Comm }
  where
    ℤ++Oinvℤ-Comm : (x y : ℤ) → (x ++ y) ≡ (y ++ x)
    ℤ++Oinvℤ-Comm O O = refl
    ℤ++Oinvℤ-Comm O (I x x₁) = refl
    ℤ++Oinvℤ-Comm (I x x₁) O = refl
    ℤ++Oinvℤ-Comm (I x x₁) (I x₂ x₃) = cong₂ I (+-comm x x₂) (+-comm x₁ x₃)
-- ---------------------------

-- ---------- Int * ----------
ℤ**-isSemiGroup : IsSemiGroup ℤ _**_
ℤ**-isSemiGroup = record { assoc = ℤ**-assoc }
  where
    ℤ**-assoc : ∀ x y z → (x ** y) ** z ≡ x ** (y ** z)
    ℤ**-assoc O O O = refl
    ℤ**-assoc O O (I x x₁) = refl
    ℤ**-assoc O (I x x₁) O = refl
    ℤ**-assoc O (I x x₁) (I x₂ x₃) = refl
    ℤ**-assoc (I x x₁) O O = refl
    ℤ**-assoc (I x x₁) O (I x₂ x₃) = refl
    ℤ**-assoc (I x x₁) (I x₂ x₃) O = refl
    ℤ**-assoc (I x x₁) (I x₂ x₃) (I x₄ x₅)
      = cong₂ I (ℤ**-assoc₁ x x₁ x₂ x₃ x₄ x₅) (ℤ**-assoc₁ x x₁ x₂ x₃ x₅ x₄)
      where
        open PropEq.≡-Reasoning
        open IsSemiGroup
        ℤ**-assoc₁ : ∀ x y z u v w →
          (x * z + y * u) * v + (x * u + y * z) * w ≡ x * (z * v + u * w) + y * (z * w + u * v)
        ℤ**-assoc₁ x y z u v w = begin
            (x * z + y * u) * v + (x * u + y * z) * w
          ≡⟨ cong (\ t → (t + (x * u + y * z) * w)) (*-distribʳ-+ v (x * z) (y * u)) ⟩
            x * z * v + y * u * v + (x * u + y * z) * w
          ≡⟨ cong (\ t → (x * z * v + y * u * v + t)) (*-distribʳ-+ w (x * u) (y * z)) ⟩
            x * z * v + y * u * v + (x * u * w + y * z * w)
          ≡⟨ +-assoc (x * z * v) (y * u * v) (x * u * w + y * z * w) ⟩
            x * z * v + (y * u * v + (x * u * w + y * z * w))
          ≡⟨ cong (\ t → ((x * z * v) + t)) (+-comm (y * u * v) (x * u * w + y * z * w)) ⟩
            x * z * v + ((x * u * w + y * z * w) + y * u * v)
          ≡⟨ sym (+-assoc (x * z * v) (x * u * w + y * z * w) (y * u * v)) ⟩
            x * z * v + (x * u * w + y * z * w) + y * u * v
          ≡⟨ sym (cong (\ t → (t + y * u * v)) ((assoc ℕ+-isSemiGroup) (x * z * v) (x * u * w) (y * z * w))) ⟩
            x * z * v + x * u * w + y * z * w + y * u * v
          ≡⟨ cong (\ t → t + x * u * w + y * z * w + y * u * v) (*-assoc x z v) ⟩
            x * (z * v) + x * u * w + y * z * w + y * u * v
          ≡⟨ cong (\ t → x * (z * v) + t + y * z * w + y * u * v) (*-assoc x u w) ⟩
            x * (z * v) + x * (u * w) + y * z * w + y * u * v
          ≡⟨ cong (\ t → x * (z * v) + x * (u * w) + t + y * u * v) (*-assoc y z w) ⟩
            x * (z * v) + x * (u * w) + y * (z * w) + y * u * v
          ≡⟨ cong (\ t → x * (z * v) + x * (u * w) + y * (z * w) + t) (*-assoc y u v) ⟩
            x * (z * v) + x * (u * w) + y * (z * w) + y * (u * v)
          ≡⟨ sym (cong (\ t → (t + y * (z * w) + y * (u * v))) (*-distribˡ-+ x (z * v) (u * w))) ⟩
            x * (z * v + u * w) + y * (z * w) + y * (u * v)
          ≡⟨ +-assoc (x * (z * v + u * w)) (y * (z * w))  (y * (u * v)) ⟩
            x * (z * v + u * w) + (y * (z * w) + y * (u * v))
          ≡⟨ sym (cong (\ t → (x * (z * v + u * w) + t)) (*-distribˡ-+ y (z * w) (u * v))) ⟩
            x * (z * v + u * w) + y * (z * w + u * v)
          ∎

ℤ**1-isMonoid : IsMonoid ℤ _**_ (I 1 0)
ℤ**1-isMonoid = record { isSemiGroup = ℤ**-isSemiGroup ; identity = (1**x≡x , x**1≡x) }
  where
    1**x≡x : (x : ℤ) → (I 1 0 ** x) ≡ x
    1**x≡x O = refl
    1**x≡x (I x x₁) = cong₂ I (x+z+z≡x x) (x+z+z≡x x₁)
      where
        x+z+z≡x : (x : ℕ) → x + 0 + 0 ≡ x
        x+z+z≡x zero = refl
        x+z+z≡x (suc x) = cong suc (x+z+z≡x x)
    x**1≡x : (x : ℤ) → (x ** I 1 0) ≡ x
    x**1≡x O = refl
    x**1≡x (I x x₁) = cong₂ I (x*1+x*0≡x x x₁) (x*0+x*1=x x x₁)
      where
        x*1+x*0≡x : (x x₁ : ℕ) → x * 1 + x₁ * 0 ≡ x
        x*1+x*0≡x zero zero = refl
        x*1+x*0≡x zero (suc x₁) = x*1+x*0≡x zero x₁
        x*1+x*0≡x (suc x) zero = cong suc (x*1+x*0≡x x zero)
        x*1+x*0≡x (suc x) (suc x₁) = x*1+x*0≡x (suc x) x₁
        x*0+x*1=x : (x x₁ : ℕ) → x * 0 + x₁ * 1 ≡ x₁
        x*0+x*1=x zero zero = refl
        x*0+x*1=x zero (suc x₁) = cong suc (x*0+x*1=x zero x₁)
        x*0+x*1=x (suc x) zero = x*0+x*1=x x zero
        x*0+x*1=x (suc x) (suc x₁) = x*0+x*1=x x (suc x₁)
-- ---------------------------

-- ---------- Int + * ----------
ℤ++0invℤ-**1-isRing : IsRing ℤ _++_ _**_ O (I 1 0) invℤ
ℤ++0invℤ-**1-isRing =
  record
    { ⊕isAbelianGroup = ℤ++Oinvℤ-isAbelianGroup
    ; ⊗isMonoid = ℤ**1-isMonoid
    ; isDistR = ℤdistR
    ; isDistL = ℤdistL }
    where
      ℤdistR : (x y z : ℤ) → (x ++ y) ** z ≡ (x ** z) ++ (y ** z)
      ℤdistR O O O = refl
      ℤdistR O O (I x x₁) = refl
      ℤdistR O (I x x₁) O = refl
      ℤdistR O (I x x₁) (I x₂ x₃) = refl
      ℤdistR (I x x₁) O O = refl
      ℤdistR (I x x₁) O (I x₂ x₃) = refl
      ℤdistR (I x x₁) (I x₂ x₃) O = refl
      ℤdistR (I x x₁) (I x₂ x₃) (I x₄ x₅) = cong₂ I (ℤdistR₁ x x₂ x₄ x₁ x₃ x₅) (ℤdistR₁ x x₂ x₅ x₁ x₃ x₄)
        where
          open PropEq.≡-Reasoning
          open IsSemiGroup
          ℤdistR₁ : (x y z u v w : ℕ) →
            (x + y) * z + (u + v) * w ≡ x * z + u * w + (y * z + v * w)
          ℤdistR₁ x y z u v w = begin
              (x + y) * z + (u + v) * w
            ≡⟨ cong (\ t → t + (u + v) * w) (*-distribʳ-+ z x y) ⟩
               x * z + y * z + (u + v) * w
            ≡⟨ cong (\ t → (x * z + y * z + t)) (*-distribʳ-+ w u v) ⟩
               x * z + y * z + (u * w + v * w)
            ≡⟨ +-assoc (x * z) (y * z) (u * w + v * w) ⟩
               x * z + (y * z + (u * w + v * w))
            ≡⟨ cong (\ t → x * z + t) (+-comm (y * z) (u * w + v * w)) ⟩
               x * z + ((u * w + v * w) + y * z)
            ≡⟨ cong (\ t → x * z + t) ((assoc ℕ+-isSemiGroup) (u * w) (v * w) (y * z)) ⟩
               x * z + (u * w + (v * w + y * z))
            ≡⟨ cong (\ t → x * z + (u * w + t)) (+-comm (v * w) (y * z)) ⟩
               x * z + (u * w + (y * z + v * w))
            ≡⟨ sym ((assoc ℕ+-isSemiGroup) (x * z) (u * w) (y * z + v * w)) ⟩
               x * z + u * w + (y * z + v * w)
            ∎
      ℤdistL : (x y z : ℤ) → x ** (y ++ z) ≡ (x ** y) ++ (x ** z)
      ℤdistL O O O = refl
      ℤdistL O O (I x x₁) = refl
      ℤdistL O (I x x₁) O = refl
      ℤdistL O (I x x₁) (I x₂ x₃) = refl
      ℤdistL (I x x₁) O O = refl
      ℤdistL (I x x₁) O (I x₂ x₃) = refl
      ℤdistL (I x x₁) (I x₂ x₃) O = refl
      ℤdistL (I x x₁) (I x₂ x₃) (I x₄ x₅) = cong₂ I (ℤdistL₁ x x₁ x₂ x₃ x₄ x₅) (ℤdistL₁ x x₁ x₃ x₂ x₅ x₄)
        where
          open PropEq.≡-Reasoning
          open IsSemiGroup
          ℤdistL₁ : (x y z u v w : ℕ) →
            x * (z + v) + y * (u + w) ≡ x * z + y * u + (x * v + y * w)
          ℤdistL₁ x y z u v w = begin
               x * (z + v) + y * (u + w)
            ≡⟨ cong (\ t → t + y * (u + w)) (*-distribˡ-+ x z v) ⟩
               x * z + x * v + y * (u + w)
            ≡⟨ cong (\ t → x * z + x * v + t) (*-distribˡ-+ y u w) ⟩
               x * z + x * v + (y * u + y * w)
            ≡⟨ +-assoc (x * z) (x * v) (y * u + y * w) ⟩
               x * z + (x * v + (y * u + y * w))
            ≡⟨ sym (cong (\ t → x * z + t) ((assoc ℕ+-isSemiGroup) (x * v) (y * u) (y * w))) ⟩
               x * z + ((x * v + y * u) + y * w)
            ≡⟨ cong (\ t → x * z + (t + y * w)) (+-comm (x * v) (y * u)) ⟩
               x * z + ((y * u + x * v) + y * w)
            ≡⟨ cong (\ t → x * z + t) ((assoc ℕ+-isSemiGroup) (y * u) (x * v) (y * w)) ⟩
               x * z + (y * u + (x * v + y * w))
            ≡⟨ sym ((assoc ℕ+-isSemiGroup) (x * z) (y * u) (x * v + y * w)) ⟩
               x * z + y * u + (x * v + y * w)
            ∎
-- ---------------------------









-- (-1) * (-1) = 1
minus : I 0 1 ** I 0 1 ≡ I 1 0
minus = refl
