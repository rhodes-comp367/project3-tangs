module Matrix-Nat where

open import Agda.Builtin.Nat using (Nat; suc; zero; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_)
open import Agda.Builtin.Equality

data Fin : Nat → Set where 
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

{- 
This program redefines each operation of the main Matrix.agda file
in terms of the matrices of natural numbers so that
the properties of matrix operations can be more easily proven.
Therefore, focus on the section "Properties of Matrix Operations with Natural Numbers."
-}

-- Matrix Definition --
Mat : Set → Nat → Nat → Set
Mat A m n = Vec (Vec A n) m

-- Matrix Addition and Subtraction --
_-_ : Nat → Nat → Nat
_-_ m zero = m
_-_ zero (suc n) = zero
_-_ (suc m) (suc n) = _-_ m n

vec-plus : {n : Nat} → Vec Nat n → Vec Nat n → Vec Nat n  
vec-plus [] _ = []
vec-plus (x ∷ xs) (y ∷ ys) = (x + y) ∷ (vec-plus xs ys)

vec-minus : {n : Nat} → Vec Nat n → Vec Nat n → Vec Nat n  
vec-minus [] _ = []
vec-minus (x ∷ xs) (y ∷ ys) = (x - y) ∷ (vec-minus xs ys)

mat-plus : {m n : Nat} → Mat Nat m n → Mat Nat m n → Mat Nat m n  
mat-plus [] _ = [] -- Other list is constrained to empty
mat-plus (r1 ∷ rs1) (r2 ∷ rs2) = vec-plus r1 r2 ∷ mat-plus rs1 rs2

mat-minus : {m n : Nat} → Mat Nat m n → Mat Nat m n → Mat Nat m n
mat-minus [] _ = []
mat-minus (r1 ∷ rs1) (r2 ∷ rs2) = (vec-minus r1 r2) ∷ (mat-minus rs1 rs2)

-- Scalar Multiplication --
vec-times : {n : Nat} → (k : Nat) → Vec Nat n → Vec Nat n  
vec-times k [] = []
vec-times k (x ∷ xs) = (k * x) ∷ (vec-times k xs)

scalar-mult : {m n : Nat} → (k : Nat) → Mat Nat m n → Mat Nat m n  
scalar-mult k [] = []
scalar-mult k (r ∷ rs) = (vec-times k r) ∷ (scalar-mult k rs)

-- Transpose --
replicate : {A : Set} → A → (n : Nat) → Vec A n
replicate x zero = []
replicate x (suc n) = x ∷ (replicate x n)

cons-col : {A : Set} → {m n : Nat} → Vec A m → Mat A m n → Mat A m (suc n)
cons-col [] m = []
cons-col (x ∷ xs) (r ∷ rs) = (x ∷ r) ∷ (cons-col xs rs)

mat-transpose : {m n : Nat} → Mat Nat m n → Mat Nat n m
mat-transpose {n = n} [] = replicate [] n
mat-transpose (r ∷ rs) = cons-col r (mat-transpose rs)

-- Matrix Multiplication --
vec-dot : {n : Nat} → Vec Nat n → Vec Nat n → Nat
vec-dot [] _ = zero
vec-dot (x ∷ xs) (y ∷ ys) = (x * y) + (vec-dot xs ys) 

row-mult : {m n : Nat} → Vec Nat n → Mat Nat m n → Vec Nat m
row-mult a [] = []
row-mult a (b ∷ bs) = vec-dot a b ∷ row-mult a bs

trans-mult : {m n r : Nat} → Mat Nat m r → Mat Nat n r → Mat Nat m n
trans-mult [] b = []
trans-mult (a ∷ as) b = row-mult a b ∷ trans-mult as b

mat-mult : {m n r : Nat} → Mat Nat m r → Mat Nat r n → Mat Nat m n
mat-mult a b = trans-mult a (mat-transpose b)


-- Properties of Matrix Operations with Natural Numbers --
-- Commutative Law for Matrix Addition
trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

suc= : ∀ {a b} → a ≡ b → suc a ≡ suc b
suc= refl = refl

plus-zero : ∀ a
  → a + 0 ≡ a
plus-zero zero = refl
plus-zero (suc a) rewrite plus-zero a = refl

plus-suc : ∀ a b
  → a + suc b ≡ suc (a + b)
plus-suc zero _ = refl
plus-suc (suc a) b rewrite plus-suc a b = refl

plus-comm : ∀ a b
  → a + b ≡ b + a
plus-comm a zero rewrite plus-zero a = refl
plus-comm a (suc b) = trans (plus-suc a b) (suc= (plus-comm a b))

vec-plus-comm : {n : Nat} → (A B : Vec Nat n) → vec-plus A B ≡ vec-plus B A
vec-plus-comm [] [] = refl
vec-plus-comm (a ∷ as) (b ∷ bs) rewrite vec-plus-comm as bs | plus-comm a b = refl

-- A + B = B + A
mat-plus-comm : {m n : Nat} → (A B : Mat Nat m n) → mat-plus A B ≡ mat-plus B A
mat-plus-comm [] [] = refl
mat-plus-comm (a ∷ as) (b ∷ bs) rewrite mat-plus-comm as bs | vec-plus-comm a b = refl

-- Associative Law for Matrix Addition
plus-assoc : ∀ a b c
  → a + (b + c) ≡ (a + b) + c
plus-assoc zero b c = refl
plus-assoc (suc a) b c rewrite plus-assoc a b c = refl

vec-plus-assoc : {n : Nat} → (A B C : Vec Nat n) → vec-plus A (vec-plus B C) ≡ vec-plus (vec-plus A B) C 
vec-plus-assoc [] b c = refl
vec-plus-assoc (a ∷ as) (b ∷ bs) (c ∷ cs) rewrite vec-plus-assoc as bs cs rewrite plus-assoc a b c = refl

-- A + (B + C) = (A + B) + C
mat-plus-assoc : {m n : Nat} → (A B C : Mat Nat m n) → mat-plus A (mat-plus B C) ≡ mat-plus (mat-plus A B) C 
mat-plus-assoc [] b c = refl
mat-plus-assoc (a ∷ as) (b ∷ bs) (c ∷ cs) rewrite mat-plus-assoc as bs cs rewrite vec-plus-assoc a b c = refl

-- Distributive Law for Scalar Multiplication over Matrix Addition
sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

times-dist1 : ∀ a b c
  → a * (b + c) ≡ a * b + a * c
times-dist1 zero b c = refl
times-dist1 (suc a) b c rewrite times-dist1 a b c | plus-assoc (b + a * b) c (a * c) | sym (plus-assoc b (a * b) c) | plus-comm (a * b) c | plus-assoc b c (a * b) | plus-assoc (b + c) (a * b) (a * c) = refl

vec-scalar-dist1 : {n : Nat} → (a : Nat) → (B : Vec Nat n) → (C : Vec Nat n) → vec-times a (vec-plus B C) ≡ vec-plus (vec-times a B) (vec-times a C) 
vec-scalar-dist1 a [] c = refl
vec-scalar-dist1 a (b ∷ bs) (c ∷ cs) rewrite vec-scalar-dist1 a bs cs | times-dist1 a b c = refl

-- a * (B + C) = a * B + a * C
mat-scalar-dist1 : {m n : Nat} → (a : Nat) → (B : Mat Nat m n) → (C : Mat Nat m n) → scalar-mult a (mat-plus B C) ≡ mat-plus (scalar-mult a B) (scalar-mult a C) 
mat-scalar-dist1 a [] c = refl
mat-scalar-dist1 a (b ∷ bs) (c ∷ cs) rewrite mat-scalar-dist1 a bs cs | vec-scalar-dist1 a b c = refl

-- Distributive Law for Scalar Multiplication over Scalar Addition
times-dist2 : ∀ a b c
  → (a + b) * c ≡ a * c + b * c
times-dist2 zero b c = refl
times-dist2 (suc a) b c rewrite times-dist2 a b c | plus-assoc c (a * c) (b * c) = refl

vec-scalar-dist2 : {n : Nat} → (a b : Nat) → (C : Vec Nat n) → vec-times (a + b) C ≡ vec-plus (vec-times a C) (vec-times b C)
vec-scalar-dist2 a b [] = refl
vec-scalar-dist2 a b (c ∷ cs) rewrite vec-scalar-dist2 a b cs | times-dist2 a b c = refl

-- (a + b) * C = a * C + b * C
mat-scalar-dist2 : {m n : Nat} → (a b : Nat) → (C : Mat Nat m n) → scalar-mult (a + b) C ≡ mat-plus (scalar-mult a C) (scalar-mult b C)
mat-scalar-dist2 a b [] = refl
mat-scalar-dist2 a b (c ∷ cs) rewrite mat-scalar-dist2 a b cs | vec-scalar-dist2 a b c = refl

-- Associative Law for Scalar Multiplication
times-assoc : ∀ a b c
  → (a * b) * c ≡ a * (b * c)
times-assoc zero b c = refl
times-assoc (suc a) b c rewrite times-dist2 b (a * b) c | times-assoc a b c = refl

vec-scalar-assoc : {n : Nat} → (a b : Nat) → (C : Vec Nat n) → vec-times (a * b) C ≡ vec-times a (vec-times b C)
vec-scalar-assoc a b [] = refl
vec-scalar-assoc a b (c ∷ cs) rewrite vec-scalar-assoc a b cs | times-assoc a b c = refl

-- (a * b) * C = a * (b * C)
mat-scalar-assoc : {m n : Nat} → (a b : Nat) → (C : Mat Nat m n) → scalar-mult (a * b) C ≡ scalar-mult a (scalar-mult b C)
mat-scalar-assoc a b [] = refl
mat-scalar-assoc a b (c ∷ cs) rewrite mat-scalar-assoc a b cs | vec-scalar-assoc a b c = refl