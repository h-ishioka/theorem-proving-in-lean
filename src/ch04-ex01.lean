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
-- short version
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
    (λ h, and.intro (λ x, (h x).left) (λ x, (h x).right))
    (λ h, λ x, and.intro (h.left x) (h.right x))



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    assume h : ∀ x, p x → q x,
    assume g : ∀ x, p x,
    show ∀ x, q x, from
        assume x,
        show q x, from (h x) (g x)
-- short version
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    λ h, λ g, λ x, (h x) (g x)



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
-- short version
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    λ h, λ x, h.elim (λ h1, or.inl (h1 x)) (λ h2, or.inr (h2 x))
