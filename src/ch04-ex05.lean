/-
5. Prove as many of the identities listed in Section 4.4 as you can.
-/

open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r :=
    assume h : ∃ x : α, r,
    exists.elim h
    (
        assume xx : α,
        id
    )
--short version
example : (∃ x : α, r) → r :=
    λ ⟨xx, hr⟩, hr



example : r → (∃ x : α, r) :=
    assume hr : r,
    exists.intro a hr
-- short version
example : r → (∃ x : α, r) :=
    λ hr, ⟨a, hr⟩



example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    iff.intro
    (
        assume h : ∃ x, p x ∧ r,
        exists.elim h
        (
            assume xx : α,
            assume h1 : p xx ∧ r,
            and.intro
            (
                show ∃ x, p x, from exists.intro xx h1.left
            )
            (
                show r, from h1.right
            )
        )
    )
    (
        assume h : (∃ x, p x) ∧ r,
        have h1 : ∃ x, p x, from h.left,
        have h2 : r, from h.right,
        exists.elim h1
        (
            assume xx : α,
            assume hpxx : p xx,
            show ∃ x, p x ∧ r, from
                exists.intro xx (and.intro hpxx h2)
        )
    )
-- short version
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    ⟨λ ⟨xx, hl, hr⟩, ⟨⟨xx, hl⟩, hr⟩, λ ⟨⟨xx, hpxx⟩, hr⟩, ⟨xx, hpxx, hr⟩⟩



example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
    (
        assume h : ∃ x, p x ∨ q x,
        exists.elim h
        (
            assume xx : α,
            assume h1 : p xx ∨ q xx,
            or.elim h1
            (
                assume h2 : p xx,
                show (∃ x, p x) ∨ (∃ x, q x), from
                    or.inl (exists.intro xx h2)
            )
            (
                assume h2 : q xx,
                show (∃ x, p x) ∨ (∃ x, q x), from
                    or.inr (exists.intro xx h2)
            )
        )
    )
    (
        assume h : (∃ x, p x) ∨ (∃ x, q x),
        or.elim h
        (
            assume h1 : ∃ x, p x,
            exists.elim h1
            (
                assume xx : α,
                assume h2 : p xx,
                show ∃ x, p x ∨ q x, from
                    exists.intro xx (or.inl h2)
            )
        )
        (
            assume h1 : ∃ x, q x,
            exists.elim h1
            (
                assume xx : α,
                assume h2 : q xx,
                show ∃ x, p x ∨ q x, from
                    exists.intro xx (or.inr h2)
            )
        )
    )
-- short version
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
    (
        λ ⟨xx, h1⟩,
        h1.elim
        (λ hpxx, or.inl ⟨xx, hpxx⟩)
        (λ hqxx, or.inr ⟨xx, hqxx⟩)
    )
    (
        λ h,
        h.elim
        (λ ⟨xx, hpxx⟩, ⟨xx, or.inl hpxx⟩)
        (λ ⟨xx, hqxx⟩, ⟨xx, or.inr hqxx⟩)
    )



example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    iff.intro
    (
        assume h : ∀ x, p x,
        show ¬ (∃ x, ¬ p x), from
            assume ⟨xx, hnpxx⟩,
            hnpxx (h xx)
    )
    (
        assume h : ¬ (∃ x, ¬ p x),
        assume xx : α,
        by_contradiction
        (
            assume h1 : ¬ p xx,
            h (exists.intro xx h1)
        )
    )
-- short version
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    iff.intro
    (
        λ h, λ ⟨xx, hnpxx⟩, hnpxx (h xx)
    )
    (
        λ h,
        λ xx,
        by_contradiction
        (λ h1, h (exists.intro xx h1))
    )



example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    iff.intro
    (
        assume h : ∃ x, p x,
        exists.elim h
        (
            assume x1 : α,
            assume hpx1 : p x1,
            show ¬ (∀ x, ¬ p x), from
                assume h1 : ∀ x, ¬ p x,
                absurd hpx1 (h1 x1)
        )
    )
    (
        assume h : ¬ (∀ x, ¬ p x),
        by_contradiction
        (
            assume h1 : ¬ ∃ x, p x,
            have h2 : ∀ x, ¬ p x, from
                assume x1,
                assume h3 : p x1,
                have h4 : ∃ x, p x, from  ⟨x1, h3⟩,
                    show false, from h1 h4,
            show false, from h h2
        )
    )
-- short version
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    iff.intro
    (
        λ ⟨x1, hpx1⟩, λ h1, absurd hpx1 (h1 x1)
    )
    (
        λ h,
        by_contradiction
        (λ h1, h (λ x1, λ h2, h1 ⟨x1, h2⟩))
    )



example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
    (
        assume h : ¬ ∃ x, p x,
        assume x1 : α,
        assume hpx1 : p x1,
        have h1 : ∃ x, p x, from
            exists.intro x1 hpx1,
        show false, from h h1
    )
    (
        assume h : ∀ x, ¬ p x,
        assume h1 : ∃ x, p x,
        exists.elim h1
        (
            assume x1 : α,
            assume hpx1 : p x1,
            show false, from (h x1) hpx1
        )
    )
-- short version
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
    (λ h, λ x1, λ hpx1, h (exists.intro x1 hpx1))
    (λ h, (λ ⟨x1, hpx1⟩, (h x1) hpx1))



example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    iff.intro
    (
        assume h : ¬ ∀ x, p x,
        by_contradiction
        (
            assume h1 : ¬ (∃ x, ¬ p x),
            have h2 : ∀ x, p x, from
                assume x1 : α,
                by_contradiction
                (
                    assume h3 : ¬ p x1,
                    h1 (exists.intro x1 h3)
                ),
            h h2
        )
    )
    (
        assume ⟨x1, hnpx1⟩,
        assume h1 : ∀ x, p x,
        absurd (h1 x1) hnpx1
    )



example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    iff.intro
    (
        assume h : ∀ x, p x → r,
        assume ⟨(x1 : α), (hpx1 : p x1)⟩,
        (h x1) hpx1
    )
    (
        assume h : (∃ x, p x) → r,
        assume x1 : α,
        assume hpx1 : p x1,
        h (exists.intro x1 hpx1)
    )



example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    iff.intro
    (
        assume ⟨(x1 : α), (h1 : p x1 → r)⟩,
        assume h2 : ∀ x, p x,
        h1 (h2 x1)
    )
    (
        assume h : (∀ x, p x) → r,
        show ∃ x, p x → r, from
            by_cases
            (
                assume h1 : ∀ x, p x, ⟨a, λ h', h h1⟩
            )
            (
                assume h1 : ¬ ∀ x, p x,
                by_contradiction
                (
                    assume h2 : ¬ ∃ x, p x → r,
                    have h3 : ∀ x, p x, from
                        assume x,
                        by_contradiction
                        (
                            assume hnp : ¬ p x,
                            have h4 : ∃ x, p x → r, from
                                ⟨x, (assume hp, absurd hp hnp)⟩,
                            show false, from h2 h4
                        ),
                    show false, from h1 h3
                )
            )
    )



example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    iff.intro
    (
        assume ⟨(x1 : α), (h1 : r → p x1)⟩,
        assume hr : r,
        exists.intro x1 (h1 hr)
    )
    (
        assume h : r → ∃ x, p x,
        by_contradiction
        (
            assume h1 : ¬ ∃ x, r → p x,
            have h2 : ∀ x, ¬ (r → p x), from
                assume x1 : α,
                assume h3 : r → p x1,
                show false, from h1 ⟨x1, h3⟩,
            have h3 : ∀ x, r ∧ ¬ p x, from
                assume x1 : α,
                (em r).elim
                (
                    assume hr : r,
                    (em (p x1)).elim
                    (assume hpx1, absurd (λ hp', hpx1) (h2 x1))
                    (assume hnpx1, ⟨hr, hnpx1⟩)
                )
                (
                    assume hnr,
                    false.elim ((h2 x1) (λ hp, absurd hp hnr))
                ),
            have h4 : ∀ x, ¬ p x, from
                assume x1 : α, (h3 x1).right,
            have hr : r, from (h3 a).left,
            match h hr with ⟨(x1 : α), (hpx1 : p x1)⟩ :=
                have hnpx1 : ¬ p x1, from h4 x1,
                hnpx1 hpx1
            end
        )
    )
