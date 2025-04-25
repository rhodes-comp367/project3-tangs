module Matrix where

open import Agda.Builtin.Nat using (Nat; suc; zero; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_)
open import Agda.Builtin.Equality 

data Fin : Nat → Set where 
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data Int : Set where
  pos  : Nat → Int
  neg : Nat → Int

-- Given i, return i + 1
isuc : Int → Int
-- i + 1 = + (n + 1)
isuc (pos n) = pos (Nat.suc n)
-- i + 1 = - 0 + 1 = + 1 
isuc (neg zero) = pos (Nat.suc zero)
-- i + 1 = - (n + 1) + 1 = - n - 1 + 1 = - n
isuc (neg (Nat.suc n)) = neg n

-- Given i, return i - 1
ipred : Int → Int
-- i - 1 = + 0 - 1 = - 1
ipred (pos zero) = neg (Nat.suc zero)
-- i - 1 = + (x + 1) - 1 = + x
ipred (pos (Nat.suc x)) = pos x
-- i - 1 = - x - 1 = - (x + 1)
ipred (neg x) = neg (Nat.suc x)

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
iplus (pos (Nat.suc m)) n = isuc (iplus (pos m) n)
iplus (neg (Nat.suc m)) n = ipred (iplus (neg m) n) 

-- Given i & j, return i - j
iminus : Int → Int → Int
iminus m n = iplus m (ineg n)

-- Given i & j, return i * j
itimes : Int → Int → Int
itimes (pos m) (pos n) = pos (m * n)
itimes (pos m) (neg n) = neg (m * n)
itimes (neg m) (pos n) = neg (m * n)
itimes (neg m) (neg n) = pos (m * n)

-- Matrix Def
Mat : Set → Nat → Nat → Set
Mat A m n = Vec (Vec A n) m

suc-vec : (n : Nat) → Vec Int n 
suc-vec zero = []
suc-vec (suc n) = (pos (suc n)) ∷ (suc-vec n)

suc-mat : (m n : Nat) → Vec (Vec Int n) m 
suc-mat zero n = [] 
suc-mat (suc m) n = suc-vec n ∷ suc-mat m n

-- Helper for mat-plus
vec-plus : {n : Nat} → Vec Int n → Vec Int n → Vec Int n  
vec-plus [] _ = []
vec-plus (x ∷ xs) (y ∷ ys) = (iplus x y) ∷ (vec-plus xs ys)

-- Helper for mat-minus
vec-minus : {n : Nat} → Vec Int n → Vec Int n → Vec Int n  
vec-minus [] _ = []
vec-minus (x ∷ xs) (y ∷ ys) = (iminus x y) ∷ (vec-minus xs ys)

vec-map : {n : Nat} → {A B : Set} → (f : A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ xs) = (f x) ∷ (vec-map f xs)

mat-map : {m n : Nat} → {A B : Set} → (f : A → B) → Mat A m n → Mat B m n
mat-map f [] = []
mat-map f (r ∷ rs) = vec-map f r ∷ mat-map f rs

-- Must be same size
mat-plus : {m n : Nat} → Mat Int m n → Mat Int m n → Mat Int m n  
mat-plus [] _ = [] -- Other list is constrained to empty
mat-plus (r1 ∷ rs1) (r2 ∷ rs2) = vec-plus r1 r2 ∷ mat-plus rs1 rs2

-- Must be same size
mat-minus : {m n : Nat} → Mat Int m n → Mat Int m n → Mat Int m n
mat-minus [] _ = []
mat-minus (r1 ∷ rs1) (r2 ∷ rs2) = (vec-minus r1 r2) ∷ (mat-minus rs1 rs2)

vec-times : {n : Nat} → (k : Int) → Vec Int n → Vec Int n  
vec-times k [] = []
vec-times k (x ∷ xs) = (itimes k x) ∷ (vec-times k xs)

mat-scalar : {m n : Nat} → (k : Int) → Mat Int m n → Mat Int m n  
mat-scalar k [] = []
mat-scalar k (r ∷ rs) = (vec-times k r) ∷ (mat-scalar k rs)

vec-dot : {n : Nat} → Vec Int n → Vec Int n → Int
vec-dot [] _ = pos zero
vec-dot (x ∷ xs) (y ∷ ys) = iplus (itimes x y) (vec-dot xs ys) 

vec-lookup : {n : Nat} → Fin n → Vec Int n → Int 
vec-lookup fzero (x ∷ _) = x
vec-lookup (fsuc k) (_ ∷ xs) = vec-lookup k xs

mat-lookup : {i j : Nat} → Fin i → Fin j → Mat Int i j → Int
mat-lookup fzero j (r ∷ rs) = vec-lookup j r
mat-lookup (fsuc i) j (r ∷ rs) = mat-lookup i j rs

vec-replace : {A : Set} → {n : Nat} → Vec A n → Fin n → A → Vec A n
vec-replace (_ ∷ xs) fzero e  = e ∷ xs
vec-replace (x ∷ xs) (fsuc k) e = x ∷ vec-replace xs k e 

mat-replace : {A : Set} → {i j : Nat} → Mat A i j → Fin i → Fin j → A → Mat A i j
mat-replace (r ∷ rs) fzero j e = (vec-replace r j e) ∷ rs
mat-replace (r ∷ rs) (fsuc i) j e = r ∷ mat-replace rs i j e

replicate : {A : Set} → A → (n : Nat) → Vec A n
replicate x zero = []
replicate x (suc n) = x ∷ (replicate x n)

cons-col : {A : Set} → {m n : Nat} → Vec A m → Mat A m n → Mat A m (suc n)
cons-col [] m = []
cons-col (x ∷ xs) (r ∷ rs) = (x ∷ r) ∷ (cons-col xs rs)

mat-transpose : {m n : Nat} → Mat Int m n → Mat Int n m
mat-transpose {n = n} [] = replicate [] n
mat-transpose (r ∷ rs) = cons-col r (mat-transpose rs)

row-mult : {m n : Nat} → Vec Int n → Mat Int m n → Vec Int m
row-mult a [] = []
row-mult a (b ∷ bs) = vec-dot a b ∷ row-mult a bs

-- Helper for mat-mult
trans-mult : {m n r : Nat} → Mat Int m r → Mat Int n r → Mat Int m n
trans-mult [] b = []
trans-mult (a ∷ as) b = row-mult a b ∷ trans-mult as b

mat-mult : {m n r : Nat} → Mat Int m r → Mat Int r n → Mat Int m n
mat-mult a b = trans-mult a (mat-transpose b)
