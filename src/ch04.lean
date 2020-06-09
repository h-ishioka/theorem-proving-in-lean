namespace ex01
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



    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
end ex01
