/-
1. Prove these equivalences:
-/

variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
    (
        assume h : ∀ x, p x ∧ q x,
        show (∀ x, p x) ∧ (∀ x, q x), from
            and.intro
            (
                show ∀ x, p x, from
                    assume x,
                    (h x).left
            )
            (
                show ∀ x, q x, from
                    assume x,
                    (h x).right
            )
    )
    (
        assume h : (∀ x, p x) ∧ (∀ x, q x),
        show ∀ x, p x ∧ q x, from
            assume x,
            and.intro (h.left x) (h.right x)
    )



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    assume h : ∀ x, p x → q x,
    assume g : ∀ x, p x,
    show ∀ x, q x, from
        assume x,
        show q x, from (h x) (g x)



example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    assume h : (∀ x, p x) ∨ (∀ x, q x),
    show ∀ x, p x ∨ q x, from
        assume x,
        h.elim
        (
            assume h1 : ∀ x, p x,
            show p x ∨ q x, from
                or.inl (h1 x)
        )
        (
            assume h2 : ∀ x, q x,
            show p x ∨ q x, from
                or.inr (h2 x)
        )
