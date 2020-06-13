/-
3. Above, we used the example vec α n for vectors of elements of type α of length n. Declare a constant vec_add that could represent a function that adds two vectors of natural numbers of the same length, and a constant vec_reverse that can represent a function that reverses its argument. Use implicit arguments for parameters that can be inferred. Declare some variables and check some expressions involving the constants that you have declared.
-/

constant vec : Type → ℕ → Type
constant vec_add : Π {α : Type} {n : ℕ}, vec α n → vec α n -> vec α n
constant vec_reverse : Π {α : Type} {n : ℕ}, vec α n → vec α n

constant v : vec ℕ 5
#check vec_add v v
#check vec_reverse v
