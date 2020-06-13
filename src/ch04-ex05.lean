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



example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
