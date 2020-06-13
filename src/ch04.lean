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

    open classical

    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) :=
        assume a : α,
        show (∀ x : α, r) ↔ r, from
            iff.intro
            (
                assume h : (∀ x : α, r),
                show r, from h a
            )
            (
                assume h : r,
                show ∀ x : α, r, from
                    assume hx : α,
                    show r, from h
            )

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
        iff.intro
        (
            assume h : ∀ x, p x ∨ r,
            or.elim (em r)
            (
                assume hr : r,
                show (∀ x, p x) ∨ r, from or.inr hr
            )
            (
                assume hnr : ¬r,
                show (∀ x, p x) ∨ r, from
                    or.inl
                    (
                        assume xx,
                        or.elim (h xx)
                        (
                            assume hpxx : p xx,
                            show p xx, from hpxx
                        )
                        (
                            assume hr : r,
                            false.elim (hnr hr)
                        )
                    )
            )
        )
        (
            assume h : (∀ x, p x) ∨ r,
            or.elim h
            (
                assume h1 : ∀ x, p x,
                show ∀ x, p x ∨ r, from
                    assume x,
                    or.inl (h1 x)
            )
            (
                assume h2 : r,
                show ∀ x, p x ∨ r, from
                    assume x : α,
                    or.inr h2
            )
        )

    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
        iff.intro
        (
            assume h : ∀ x, r → p x,
            show r → ∀ x, p x, from
                assume hr : r,
                show ∀ x, p x, from
                    assume xx : α,
                    (h xx) hr
        )
        (
            assume h : r → ∀ x, p x,
            show ∀ x, r → p x, from
                assume xx : α,
                assume hr : r,
                (h hr) xx
        )

end ex02
