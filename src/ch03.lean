namespace ex01
    /-
    1. Prove the following identities, replacing the “sorry” placeholders with actual proofs.
    -/

    variables p q r : Prop

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p :=
        iff.intro
        (
            assume h : p ∧ q,
            show q ∧ p, from and.intro (and.elim_right h) (and.elim_left h)
        )
        (
            assume h : q ∧ p,
            show p ∧ q, from and.intro (and.elim_right h) (and.elim_left h)
        )
    -- short version
    example : p ∧ q ↔ q ∧ p :=
        iff.intro (λ h, ⟨h.right, h.left⟩) (λ h, ⟨h.right, h.left⟩)



    example : p ∨ q ↔ q ∨ p :=
        iff.intro
        (
            assume h : p ∨ q,
            or.elim h
            (assume hp : p, show q ∨ p, from or.intro_right q hp)
            (assume hq : q, show q ∨ p, from or.intro_left p hq)
        )
        (
            assume h : q ∨ p,
            or.elim h
            (assume hq : q, show p ∨ q, from or.intro_right p hq)
            (assume hp : p, show p ∨ q, from or.intro_left q hp)
        )
    -- short version
    example : p ∨ q ↔ q ∨ p :=
        iff.intro
        (λ h, h.elim (λ hp, or.inr hp) (λ hq, or.inl hq))
        (λ h, h.elim (λ hq, or.inr hq) (λ hp, or.inl hp))



    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
        iff.intro
        (
            assume hl : (p ∧ q) ∧ r,
            and.intro
            (and.elim_left (and.elim_left hl))
            (and.intro (and.elim_right (and.elim_left hl)) (and.elim_right hl))
        )
        (
            assume hr : p ∧ (q ∧ r),
            and.intro
            (and.intro (and.elim_left hr) (and.elim_left (and.elim_right hr)))
            (and.elim_right (and.elim_right hr))
        )
    -- short vertion
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
        iff.intro
        (λ hl, ⟨hl.left.left, ⟨hl.left.right, hl.right⟩⟩)
        (λ hr, ⟨⟨hr.left, hr.right.left⟩, hr.right.right⟩)



    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
        iff.intro
        (
            assume h : (p ∨ q) ∨ r,
            or.elim h
            (
                assume hpq : p ∨ q,
                or.elim hpq
                (
                    assume hp : p,
                    show p ∨ (q ∨ r), from or.intro_left (q ∨ r) hp
                )
                (
                    assume hq : q,
                    show p ∨ (q ∨ r), from or.intro_right p (or.intro_left r hq)
                )
            )
            (
                assume hr : r,
                show p ∨ (q ∨ r), from or.intro_right p (or.intro_right q hr)
            )
        )
        (
            assume h : p ∨ (q ∨ r),
            or.elim h
            (
                assume hp : p,
                show (p ∨ q) ∨ r, from or.intro_left r (or.intro_left q hp)
            )
            (
                assume hqr : (q ∨ r),
                or.elim hqr
                (
                    assume hq : q,
                    show (p ∨ q) ∨ r, from or.intro_left r (or.intro_right p hq)
                )
                (
                    assume hr : r,
                    show (p ∨ q) ∨ r, from or.intro_right (p ∨ q) hr
                )
            )
        )
    -- short version
    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
        iff.intro
        (
            λ h,
            h.elim
            (λ hpq, hpq.elim (λ hp, or.inl hp) (λ hq, or.inr (or.inl hq)))
            (λ hr, or.inr (or.inr hr))
        )
        (
            λ h,
            h.elim
            (λ hp, or.inl (or.inl hp))
            (λ hqr, hqr.elim (λ hq, or.inl (or.inr hq)) (λ hr, or.inr hr))
        )



    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
        iff.intro
        (
            assume h : p ∧ (q ∨ r),
            have hp : p, from and.elim_left h,
            have hqr : q ∨ r, from and.elim_right h,
            or.elim hqr
            (
                assume hq : q,
                show (p ∧ q) ∨ (p ∧ r), from or.intro_left (p ∧ r) (and.intro hp hq)
            )
            (
                assume hr : r,
                show (p ∧ q) ∨ (p ∧ r), from or.intro_right (p ∧ q) (and.intro hp hr)
            )
        )
        (
            assume h : (p ∧ q) ∨ (p ∧ r),
            or.elim h
            (
                assume hpq : p ∧ q,
                have hp : p, from and.elim_left hpq,
                have hq : q, from and.elim_right hpq,
                have hqr : q ∨ r, from or.intro_left r hq,
                show p ∧ (q ∨ r), from and.intro hp hqr
            )
            (
                assume hpr : p ∧ r,
                have hp : p, from and.elim_left hpr,
                have hr : r, from and.elim_right hpr,
                have hqr : q ∨ r, from or.intro_right q hr,
                show p ∧ (q ∨ r), from and.intro hp hqr
            )
        )
    -- short version
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
        iff.intro
        (
            λ h,
            h.right.elim
            (λ hq, or.inl ⟨h.left, hq⟩)
            (λ hr, or.inr ⟨h.left, hr⟩)
        )
        (
            λ h,
            h.elim
            (λ hpq, ⟨hpq.left, or.inl hpq.right⟩)
            (λ hpr, ⟨hpr.left, or.inr hpr.right⟩)
        )



    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
        iff.intro
        (
            assume h : p ∨ (q ∧ r),
            h.elim
            (
                assume hp : p,
                show (p ∨ q) ∧ (p ∨ r), from ⟨or.inl hp, or.inl hp⟩
            )
            (
                assume hqr : q ∧ r,
                show (p ∨ q) ∧ (p ∨ r), from ⟨or.inr hqr.left, or.inr hqr.right⟩
            )
        )
        (
            assume h : (p ∨ q) ∧ (p ∨ r),
            have hpq : p ∨ q, from h.left,
            have hpr : p ∨ r, from h.right,
            hpq.elim
            (
                assume hp : p,
                show p ∨ (q ∧ r), from or.inl hp
            )
            (
                assume hq : q,
                hpr.elim
                (
                    assume hp : p,
                    show p ∨ (q ∧ r), from or.inl hp
                )
                (
                    assume hr : r,
                    show p ∨ (q ∧ r), from or.inr ⟨hq, hr⟩
                )
            )
        )
    -- short version
    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
        iff.intro
        (
            λ h,
            h.elim
            (λ hp, ⟨or.inl hp, or.inl hp⟩)
            (λ hqr, ⟨or.inr hqr.left, or.inr hqr.right⟩)
        )
        (
            λ h,
            h.left.elim
            (λ hp, or.inl hp)
            (λ hq, h.right.elim (λ hp, or.inl hp) (λ hr, or.inr ⟨hq, hr⟩))
        )



    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) :=
        iff.intro
        (
            assume h : p → (q → r),
            assume hpq : p ∧ q,
            show r, from h hpq.left hpq.right
        )
        (
            assume h : p ∧ q → r,
            assume hp : p,
            assume hq : q,
            show r, from h ⟨hp, hq⟩
        )
    -- short version
    example : (p → (q → r)) ↔ (p ∧ q → r) :=
        iff.intro
        (λ h, λ hpq, h hpq.left hpq.right)
        (λ h : p ∧ q → r, λ hp : p, λ hq : q, h ⟨hp, hq⟩)



    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
        iff.intro
        (
            assume h : (p ∨ q) → r,
            have hpr : p → r, from
                assume hp : p,
                show r, from h (or.inl hp),
            have hqr : q → r, from
                assume hq : q,
                show r, from h (or.inr hq),
            ⟨hpr, hqr⟩
        )
        (
            assume h : (p → r) ∧ (q → r),
            assume hpq : p ∨ q,
            have hpr : p → r, from h.left,
            have hqr : q → r, from h.right,
            hpq.elim
            (
                assume hp : p,
                show r, from hpr hp
            )
            (
                assume hq : q,
                show r, from hqr hq
            )
        )
    -- short version
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
        iff.intro
        (λ h, ⟨λ hp : p, h (or.inl hp), λ hq : q, h (or.inr hq)⟩)
        (λ h, λ hpq, hpq.elim (λ hp : p, h.left hp) (λ hq : q, h.right hq))



    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
        iff.intro
        (
            assume h : ¬(p ∨ q),
            and.intro
            (
                assume hp : p,
                show false, from h (or.inl hp)
            )
            (
                assume hq : q,
                show false, from h (or.inr hq)
            )
        )
        (
            assume h : ¬p ∧ ¬q,
            assume g : p ∨ q,
            show false, from
                g.elim
                (
                    assume hp : p,
                    h.left hp
                )
                (
                    assume hq : q,
                    h.right hq
                )
        )
    -- short version
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
        iff.intro
        (λ h, ⟨(λ hp, h (or.inl hp)), (λ hq, h (or.inr hq))⟩)
        (λ h, λ g, g.elim (λ hp, h.left hp) (λ hq, h.right hq))



    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
        assume h : ¬p ∨ ¬q,
        assume g : p ∧ q,
        h.elim
        (
            assume hnp : ¬p,
            show false, from hnp g.left
        )
        (
            assume hnq : ¬q,
            show false, from hnq g.right
        )
    -- short version
    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
        λ h, λ g, h.elim (λ hnp, hnp g.left) (λ hnq, hnq g.right)



    example : ¬(p ∧ ¬p) :=
        assume h : p ∧ ¬p,
        h.right h.left
    -- short version
    example : ¬(p ∧ ¬p) :=
        λ h, h.right h.left



    example : p ∧ ¬q → ¬(p → q) :=
        assume h : p ∧ ¬q,
        assume g : p → q,
        show false, from h.right (g h.left)
    -- short version
    example : p ∧ ¬q → ¬(p → q) :=
        λ h, λ g, h.right (g h.left)


    example : ¬p → (p → q) :=
        assume hnp : ¬p,
        assume hp : p,
        show q, from false.elim (hnp hp)
    -- short version
    example : ¬p → (p → q) :=
        λ hnp, λ hp, absurd hp hnp



    example : (¬p ∨ q) → (p → q) :=
        assume h : ¬p ∨ q,
        assume hp : p,
        h.elim
        (
            assume hnp : ¬p,
            show q, from false.elim (hnp hp)
        )
        (
            assume hq : q,
            show q, from hq
        )
    -- short version
    example : (¬p ∨ q) → (p → q) :=
        λ h, λ hp : p, h.elim (λ hnp, absurd hp hnp) (λ hq, hq)



    example : p ∨ false ↔ p :=
        iff.intro
        (
            assume h : p ∨ false,
            h.elim
            (
                assume hp : p,
                show p, from hp
            )
            (
                assume hf : false,
                false.elim hf
            )
        )
        (
            assume hp : p,
            show p ∨ false, from or.inl hp
        )
    -- short version
    example : p ∨ false ↔ p :=
        iff.intro
        (λ h, h.elim (λ hp, hp) (λ hf, false.elim hf))
        (λ hp, or.inl hp)



    example : p ∧ false ↔ false :=
        iff.intro
        (
            assume h : p ∧ false,
            h.right
        )
        (
            assume h : false,
            false.elim h
        )
    -- short version
    example : p ∧ false ↔ false :=
        iff.intro
        (λ h, h.right)
        (λ h, false.elim h)



    example : (p → q) → (¬q → ¬p) :=
        assume h : p → q,
        assume hnq : ¬q,
        assume hp : p,
        hnq (h hp)
end ex01

namespace ex02
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
end ex02

namespace ex03
    /-
    3. Prove ¬(p ↔ ¬p) without using classical logic.
    -/

    variables p : Prop

    example : ¬(p ↔ ¬p) :=
        assume hpiffnp : p ↔ ¬p,
        have hpimplnp : p → ¬p, from iff.elim_left hpiffnp,
        have hnpimplp : ¬p → p, from iff.elim_right hpiffnp,
        have hnp : ¬p, from
            assume hp : p,
            show false, from absurd hp (hpimplnp hp),
        have hp : p, from hnpimplp hnp,
        absurd hp hnp
end ex03
