/-
4. Similarly, declare a constant matrix so that matrix α m n could represent the type of m by n matrices. Declare some constants to represent functions on this type, such as matrix addition and multiplication, and (using vec) multiplication of a matrix by a vector. Once again, declare some variables and check some expressions involving the constants that you have declared.
-/

constant matrix : Type -> ℕ -> ℕ -> Type
constant mat_add : Π {α : Type} {m : ℕ} {n : ℕ}, matrix α m n -> matrix α m n -> matrix α m n
constant mat_mul : Π {α : Type} {l : ℕ} {m : ℕ} {n : ℕ}, matrix α l m -> matrix α m n -> matrix α l n

constant X : matrix ℕ 4 5
constant Y : matrix ℕ 4 5
constant Z : matrix ℕ 5 6

#check mat_add X Y
#check mat_mul X Z
