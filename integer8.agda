module integer8 where

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl)
open import Data.Nat

-- minus
data Neg : Set where
  N : ℕ → Neg

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
-- productInt
_**_ : Int → Int → Int
O ** O = O
O ** _ = O
_ ** O = O
I x y ** I z w = I (x * z + y * w) (x * w + y * z)

-- (-1) ** (-1) = 1
minus : I 0 1 ** I 0 1 ≡ I 1 0
minus = refl
