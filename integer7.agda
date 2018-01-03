module integer7 where

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong; sym)
open import Data.Nat

-- Int
data Int : Set where
  O : Int
  I : ℕ → ℕ → Int
postulate
  zeroZ : (x : ℕ) → I x x ≡ O
-- plusInt
_++_ : Int → Int → Int
O ++ O = O
O ++ X = X
X ++ O = X
I x y ++ I z w = I (x + z) (y + w)
postulate
  ++Assoc : (X Y Z : Int) → (X ++ Y) ++ Z ≡ X ++ (Y ++ Z)
  ++Comm : (X Y : Int) → X ++ Y ≡ Y ++ X
-- productInt
_**_ : Int → Int → Int
O ** O = O
O ** _ = O
_ ** O = O
I x y ** I z w = I (x * z + y * w) (x * w + y * z)
postulate
  **Assoc : (X Y Z : Int) → (X ** Y) ** Z ≡ X ** (Y ** Z)
  **Dist : (X Y Z : Int) → X ** (Y ++ Z) ≡ (X ** Y) ++ (X ** Z)

-- (-1) ** (-1) = 1
minus1 : I 0 1 ** I 0 1 ≡ I 1 0
minus1 = refl
-1+1 : I 0 1 ++ I 1 0 ≡ I 1 1
-1+1 = refl
-1*1 : I 0 1 ** I 1 0 ≡ I 0 1
-1*1 = refl
minus2 : I 0 1 ** I 0 1 ≡ I 1 0
minus2 = begin
    I 0 1 ** I 0 1
  ≡⟨ refl ⟩
    (I 0 1 ** I 0 1) ++ O
  ≡⟨ sym (cong (\ x → (I 0 1 ** I 0 1) ++ x) (zeroZ 1)) ⟩
    (I 0 1 ** I 0 1) ++ (I 1 1)
  ≡⟨ sym (cong (\ x → (I 0 1 ** I 0 1) ++ x) -1+1) ⟩
    (I 0 1 ** I 0 1) ++ (I 0 1 ++ I 1 0)
  ≡⟨ sym (++Assoc O O (I (suc (suc zero)) (suc zero))) ⟩
    ((I 0 1 ** I 0 1) ++ I 0 1) ++ I 1 0
  ≡⟨ sym (cong (\ x → ((I 0 1 ** I 0 1) ++ x) ++ I 1 0) -1*1) ⟩
    ((I 0 1 ** I 0 1) ++ (I 0 1 ** I 1 0)) ++ I 1 0
  ≡⟨ sym (cong (\ x → x ++ I 1 0) (**Dist (I 0 1) (I 0 1) (I 1 0))) ⟩
    (I 0 1 ** (I 0 1 ++ I 1 0)) ++ I 1 0
  ≡⟨ refl ⟩
    (I 0 1 ** I 1 1) ++ I 1 0
  ≡⟨ cong (\ x → ((I 0 1 ** x) ++ I 1 0)) (zeroZ 1) ⟩
    (I 0 1 ** O) ++ I 1 0
  ≡⟨ refl ⟩
    O ++ I 1 0
  ≡⟨ refl ⟩
    I 1 0
  ∎
  where open PropEq.≡-Reasoning
