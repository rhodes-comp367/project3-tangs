module Matrix where

open import Agda.Builtin.Nat using (Nat; suc; zero; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_)
open import Agda.Builtin.Equality
open import Int 

data Fin : Nat → Set where 
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

-- Matrix Definition --
Mat : Set → Nat → Nat → Set
Mat A m n = Vec (Vec A n) m

-- Extra Vector/Matrix Functions --
zero-vec : (n : Nat) → Vec Nat n
zero-vec zero = []
zero-vec (suc n) = 0 ∷ zero-vec n

-- Zero Matrix
zero-mat : (m n : Nat) → Vec (Vec Nat n) m
zero-mat zero n = []
zero-mat (suc m) n = zero-vec n ∷ zero-mat m n

suc-vec : (n : Nat) → Vec Int n 
suc-vec zero = []
suc-vec (suc n) = (pos (suc n)) ∷ (suc-vec n)

-- Repeated Decreasing Sequence Matrix
-- Used to test matrix operations with values
suc-mat : (m n : Nat) → Vec (Vec Int n) m 
suc-mat zero n = [] 
suc-mat (suc m) n = suc-vec n ∷ suc-mat m n

vec-map : {n : Nat} → {A B : Set} → (f : A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ xs) = (f x) ∷ (vec-map f xs)

mat-map : {m n : Nat} → {A B : Set} → (f : A → B) → Mat A m n → Mat B m n
mat-map f [] = []
mat-map f (r ∷ rs) = vec-map f r ∷ mat-map f rs

-- Find entry at index k in the vector
vec-lookup : {n : Nat} → Fin n → Vec Int n → Int 
vec-lookup fzero (x ∷ _) = x
vec-lookup (fsuc k) (_ ∷ xs) = vec-lookup k xs

-- Find entry at row i and column j in the matrix
mat-lookup : {i j : Nat} → Fin i → Fin j → Mat Int i j → Int
mat-lookup fzero j (r ∷ rs) = vec-lookup j r
mat-lookup (fsuc i) j (r ∷ rs) = mat-lookup i j rs

-- Replace entry at index k in the vector
vec-replace : {A : Set} → {n : Nat} → Vec A n → Fin n → A → Vec A n
vec-replace (_ ∷ xs) fzero e  = e ∷ xs
vec-replace (x ∷ xs) (fsuc k) e = x ∷ vec-replace xs k e 

-- Replace entry at row i and column j in the matrix
mat-replace : {A : Set} → {i j : Nat} → Mat A i j → Fin i → Fin j → A → Mat A i j
mat-replace (r ∷ rs) fzero j e = (vec-replace r j e) ∷ rs
mat-replace (r ∷ rs) (fsuc i) j e = r ∷ mat-replace rs i j e


-- Matrix Addition and Subtraction --
vec-plus : {n : Nat} → Vec Int n → Vec Int n → Vec Int n  
vec-plus [] _ = []
vec-plus (x ∷ xs) (y ∷ ys) = (iplus x y) ∷ (vec-plus xs ys)

vec-minus : {n : Nat} → Vec Int n → Vec Int n → Vec Int n  
vec-minus [] _ = []
vec-minus (x ∷ xs) (y ∷ ys) = (iminus x y) ∷ (vec-minus xs ys)

mat-plus : {m n : Nat} → Mat Int m n → Mat Int m n → Mat Int m n  
mat-plus [] _ = [] -- Other list is constrained to empty
mat-plus (r1 ∷ rs1) (r2 ∷ rs2) = vec-plus r1 r2 ∷ mat-plus rs1 rs2

mat-minus : {m n : Nat} → Mat Int m n → Mat Int m n → Mat Int m n
mat-minus [] _ = []
mat-minus (r1 ∷ rs1) (r2 ∷ rs2) = (vec-minus r1 r2) ∷ (mat-minus rs1 rs2)

-- Scalar Multiplication --
vec-times : {n : Nat} → (k : Int) → Vec Int n → Vec Int n  
vec-times k [] = []
vec-times k (x ∷ xs) = (itimes k x) ∷ (vec-times k xs)

scalar-mult : {m n : Nat} → (k : Int) → Mat Int m n → Mat Int m n  
scalar-mult k [] = []
scalar-mult k (r ∷ rs) = (vec-times k r) ∷ (scalar-mult k rs)

-- Transpose --
replicate : {A : Set} → A → (n : Nat) → Vec A n
replicate x zero = []
replicate x (suc n) = x ∷ (replicate x n)

cons-col : {A : Set} → {m n : Nat} → Vec A m → Mat A m n → Mat A m (suc n)
cons-col [] m = []
cons-col (x ∷ xs) (r ∷ rs) = (x ∷ r) ∷ (cons-col xs rs)

-- Switches the rows and columns of a matrix
mat-transpose : {m n : Nat} → Mat Int m n → Mat Int n m
mat-transpose {n = n} [] = replicate [] n
mat-transpose (r ∷ rs) = cons-col r (mat-transpose rs)

-- Matrix Multiplication --
vec-dot : {n : Nat} → Vec Int n → Vec Int n → Int
vec-dot [] _ = pos zero
vec-dot (x ∷ xs) (y ∷ ys) = iplus (itimes x y) (vec-dot xs ys) 

-- Dot product row a to each row of second matrix
row-mult : {m n : Nat} → Vec Int n → Mat Int m n → Vec Int m
row-mult a [] = []
row-mult a (b ∷ bs) = vec-dot a b ∷ row-mult a bs

-- Dot product every row of first matrix to each row of second matrix
trans-mult : {m n r : Nat} → Mat Int m r → Mat Int n r → Mat Int m n
trans-mult [] b = []
trans-mult (a ∷ as) b = row-mult a b ∷ trans-mult as b

-- Transpose second matrix in order to easily multiply
-- each column of the second matrix by each row of the first matrix
-- because the rows of our defined matrix are more easily accessible
mat-mult : {m n r : Nat} → Mat Int m r → Mat Int r n → Mat Int m n
mat-mult a b = trans-mult a (mat-transpose b)


-- Determinant of Matrix --
to-nat : {n : Nat} → Fin n → Nat
to-nat fzero = 0
to-nat (fsuc n) = suc (to-nat n)

fmax : (n : Nat) → Fin (suc n)
fmax zero = fzero
fmax (suc n) = fsuc (fmax n)

-- Get a fin that is of size m but also less than suc n
-- If m is larger than n, than fin is of size n
to-fin : (m n : Nat) → Fin (suc n)
to-fin zero n = fzero
to-fin (suc m) zero = fzero
to-fin (suc m) (suc n) = fsuc (to-fin m n)

-- sign-calc : i j → + or -
sign : ∀ i j → Int
sign i j = ipower (i + j) (neg 1)

-- Delete row function
vec-delete : {A : Set} → {n : Nat} → Fin (suc n) → Vec A (suc n) → Vec A n
vec-delete fzero (_ ∷ ys) = ys
vec-delete {_} {suc _} (fsuc k) (x ∷ xs) = x ∷ (vec-delete k xs)

-- Delete column function
delete-col : {m n : Nat} → Fin (suc n) → Mat Int m (suc n) → Mat Int m n 
delete-col f A = mat-transpose (vec-delete f (mat-transpose A))

-- Submatrix that remains after deleting first row and jth column
submatrix : {n : Nat} → Fin (suc n) → Mat Int (suc n) (suc n) → Mat Int n n
submatrix j a = vec-delete fzero (delete-col j a)

-- Find determinant of matrix by cofactor expansion along the first row for n >= 3
-- To get the determinant, Fin j has to be Fin n (e.g., fmax (n - 1)) because the indices start at 0
det : {n j : Nat} → Fin j → Mat Int n n → Int
det _ [] = pos 1
det {suc zero} _ ((x ∷ []) ∷ []) = x
det {suc (suc zero)} _ ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ []) = iminus (itimes a d) (itimes b c)
det {suc (suc (suc n))} {j} fzero ((x ∷ r) ∷ rs) = itimes (sign 0 0) (itimes x (det {suc (suc n)} {j} fzero (submatrix fzero ((x ∷ r) ∷ rs))))
det {suc (suc (suc n))} (fsuc k) ((x ∷ r) ∷ rs) = iplus (itimes ((sign 0 (to-nat (fsuc k)))) (itimes (vec-lookup (to-fin (to-nat (fsuc k)) (suc (suc n))) (x ∷ r)) (det {suc (suc n)} k (submatrix (to-fin (to-nat (fsuc k)) (suc (suc n))) ((x ∷ r) ∷ rs))))) (det k (((x ∷ r) ∷ rs)))