/-
2. Prove the following identities, replacing the “sorry” placeholders with actual proofs. These require classical reasoning.
-/

open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    assume h : p → r ∨ s,
    (em p).elim
    (
        assume hp : p,
        have hrs : r ∨ s, from h hp,
        hrs.elim
        (
            assume hr : r,
            show (p → r) ∨ (p → s),
            from or.inl (assume hp : p, hr)
        )
        (
            assume hs : s,
            show (p → r) ∨ (p → s),
            from or.inr (assume hp : p, hs)
        )
    )
    (
        assume hnp : ¬p,
        suffices hpr : p → r, from or.inl hpr,
        show p → r, from
            assume hp : p,
            show r, from false.elim (hnp hp)
    )
-- short version
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    λ h,
    (em p).elim
    (
        λ hp,
        (h hp).elim
        (λ hr, or.inl (λ hp : p, hr))
        (λ hs, or.inr (λ hp : p, hs))
    )
    (λ hnp, or.inl (λ hp, absurd hp hnp))



example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    assume h : ¬(p ∧ q),
    or.elim (em p)
    (
        assume hp : p,
        have hnq : ¬q, from
            assume hq : q,
            h ⟨hp, hq⟩,
        or.inr hnq
    )
    (
        assume hnp : ¬p,
        or.inl hnp
    )
-- short version
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    λ h,
    or.elim (em p)
    (λ hp, or.inr (λ hq, h ⟨hp, hq⟩))
    (λ hnp, or.inl hnp)



example : ¬(p → q) → p ∧ ¬q :=
    assume h : ¬(p → q),
    (em p).elim
    (
        assume hp : p,
        (em q).elim
        (
            assume hq : q,
            have hpimplq : p → q, from
                assume hp' : p,
                hq,
            show p ∧ ¬q, from false.elim (h hpimplq)
        )
        (
            assume hnq : ¬q,
            show p ∧ ¬q, from ⟨hp, hnq⟩
        )
    )
    (
        assume hnp : ¬p,
        have hpimplq : p → q, from
            assume hp : p,
            false.elim (hnp hp),
        false.elim (h hpimplq)
    )
-- short version
example : ¬(p → q) → p ∧ ¬q :=
    λ h,
    (em p).elim
    (
        λ hp : p,
        (em q).elim
        (λ hq, absurd (λ hp', hq) h)
        (λ hnq, ⟨hp, hnq⟩)
    )
    (
        λ hnp,
        false.elim (h (λ hp, absurd hp hnp))
    )



example : (p → q) → (¬p ∨ q) :=
    assume h : p → q,
    (em p).elim
    (
        assume hp : p,
        or.inr (h hp)
    )
    (
        assume hnp : ¬p,
        or.inl hnp
    )
-- short version
example : (p → q) → (¬p ∨ q) :=
    λ h,
    (em p).elim
    (λ hp, or.inr (h hp))
    (λ hnp, or.inl hnp)



example : (¬q → ¬p) → (p → q) :=
    assume h : ¬q → ¬p,
    assume hp : p,
    (em q).elim
    (
        assume hq : q,
        hq
    )
    (
        assume hnq : ¬q,
        absurd hp (h hnq)
    )
-- short version
example : (¬q → ¬p) → (p → q) :=
    λ h,
    λ hp,
    (em q).elim
    id
    (λ hnq, absurd hp (h hnq))



example : p ∨ ¬p :=
    em p



example : (((p → q) → p) → p) :=
    assume h : (p → q) → p,
    (em p).elim
    (
        assume hp : p,
        hp
    )
    (
        assume hnp : ¬p,
        have hpimplq : p → q, from
            assume hp : p,
            absurd hp hnp,
        absurd (h hpimplq) hnp
    )
-- short version
example : (((p → q) → p) → p) :=
    λ h,
    (em p).elim
    id
    (λ hnp, absurd (h (λ hp : p, absurd hp hnp)) hnp)
