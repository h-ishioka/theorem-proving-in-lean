namespace ex01
    /-
    1. Define the function Do_Twice, as described in Section 2.4.
    -/

    def Do_Twice : Π {α : Type}, (α → α) → (α → α)
        := λ α f x, f (f x)
end ex01

namespace ex02
    /-
    2. Define the functions curry and uncurry, as described in Section 2.4.
    -/

    def curry (α β γ : Type) (f : α × β → γ) : α → β → γ
        := λ x y, f (x, y)
    def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ
        := λ pair, f pair.1 pair.2
end ex02

namespace ex03
    /-
    3. Above, we used the example vec α n for vectors of elements of type α of length n. Declare a constant vec_add that could represent a function that adds two vectors of natural numbers of the same length, and a constant vec_reverse that can represent a function that reverses its argument. Use implicit arguments for parameters that can be inferred. Declare some variables and check some expressions involving the constants that you have declared.
    -/

    constant vec : Type → ℕ → Type
    constant vec_add : Π {α : Type} {n : ℕ}, vec α n → vec α n -> vec α n
    constant vec_reverse : Π {α : Type} {n : ℕ}, vec α n → vec α n

    constant v : vec ℕ 5
    #check vec_add v v
    #check vec_reverse v
end ex03

namespace ex04
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
end ex04
