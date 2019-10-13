module Chunk where

open import Codata.Stream using (chunksOf; iterate; take)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)


-- mylist 3 = [[1,2,3],[4,5,6],[7,8,9]]
myVec : (n : ℕ) → Vec (Vec ℕ n) n
myVec n = take n (chunksOf n (iterate suc 1))




