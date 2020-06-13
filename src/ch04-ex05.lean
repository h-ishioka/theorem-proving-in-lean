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
    λ h, exists.elim h (λ xx : α, id)



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
    iff.intro
    (
        λ h,
        exists.elim h
        (
            λ xx,
            λ h1,
            and.intro
            (exists.intro xx h1.left)
            (h1.right)
        )
    )
    (
        λ h,
        exists.elim h.left
        (λ xx, λ hpxx, ⟨xx, (and.intro hpxx h.right)⟩)
    )



example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
