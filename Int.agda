module Int where

open import Agda.Builtin.Nat using (Nat; suc; zero; _+_; _*_)

data Int : Set where
  pos : Nat → Int
  neg : Nat → Int

-- Given i, return i + 1
isuc : Int → Int
-- i + 1 = + (n + 1)
isuc (pos n) = pos (suc n)
-- i + 1 = - 0 + 1 = + 1 
isuc (neg zero) = pos (suc zero)
-- i + 1 = - (n + 1) + 1 = - n - 1 + 1 = - n
isuc (neg (suc n)) = neg n

-- Given i, return i - 1
ipred : Int → Int
-- i - 1 = + 0 - 1 = - 1
ipred (pos zero) = neg (suc zero)
-- i - 1 = + (x + 1) - 1 = + x
ipred (pos (suc x)) = pos x
-- i - 1 = - x - 1 = - (x + 1)
ipred (neg x) = neg (suc x)

-- Given i, return -i
ineg : Int → Int
-- - i = - (+ x) = - x
ineg (pos x) = neg x
-- - i = - (- x) = + x 
ineg (neg x) = pos x

-- Given i & j, return i + j
iplus : Int → Int → Int
iplus (pos zero) n = n
iplus (neg zero) n = n 
iplus (pos (suc m)) n = isuc (iplus (pos m) n)
iplus (neg (suc m)) n = ipred (iplus (neg m) n) 

-- Given i & j, return i - j
iminus : Int → Int → Int
iminus m n = iplus m (ineg n)

-- Given i & j, return i * j
itimes : Int → Int → Int
itimes (pos m) (pos n) = pos (m * n)
itimes (pos m) (neg n) = neg (m * n)
itimes (neg m) (pos n) = neg (m * n)
itimes (neg m) (neg n) = pos (m * n)

ipower : Nat → Int → Int
ipower zero x = pos 1
ipower (suc n) x = itimes x (ipower n x)