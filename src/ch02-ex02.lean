/-
2. Define the functions curry and uncurry, as described in Section 2.4.
-/

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ
    := λ x y, f (x, y)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ
    := λ pair, f pair.1 pair.2
