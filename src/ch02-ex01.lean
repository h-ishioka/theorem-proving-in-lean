/-
1. Define the function Do_Twice, as described in Section 2.4.
-/

def Do_Twice : Π {α : Type}, (α → α) → (α → α)
    := λ α f x, f (f x)
