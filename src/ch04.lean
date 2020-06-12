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
end ex01

namespace ex02
    /-
    2. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
    -/

    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) := sorry
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
end ex02
