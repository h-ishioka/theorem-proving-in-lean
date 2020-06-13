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
-- short version
example : α → ((∀ x : α, r) ↔ r) :=
    λ a, iff.intro (λ h, h a) (λ h, λ hx, h)



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
-- shor version
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
    (
        λ h,
        (em r).elim
        (
            λ hr : r,
            or.inr hr
        )
        (
            λ hnr : ¬r,
            or.inl (λ xx, (h xx).elim id (λ hr, absurd hr hnr) )
        )
    )
    (
        λ h, or.elim h (λ h1, λ x, or.inl (h1 x)) (λ h2, λ x, or.inr h2)
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
-- short version
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    ⟨(λ h, λ hr, λ xx, (h xx) hr), (λ h, λ xx, λ hr, (h hr) xx)⟩
