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
