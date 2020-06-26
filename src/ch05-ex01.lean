/-
1. Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you can now with tactic proofs, using also rw and simp as appropriate.
-/

import data.int.basic

namespace ch03_ex01
    variables p q r : Prop

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hp hq,
        constructor,
        repeat { assumption },
        -- <-
        intro h,
        cases h with hp hq,
        constructor,
        repeat { assumption }
    end

    example : p ∨ q ↔ q ∨ p :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hp hq,
        right,
        exact hp,
        left,
        exact hq,
        -- <-
        intro h,
        cases h with hq hp,
        right,
        exact hq,
        left,
        exact hp
    end

    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hpq hr,
        cases hpq with hp hq,
        constructor,
        exact hp,
        constructor,
        repeat { assumption },
        -- <-
        intro h,
        cases h with hp hqr,
        cases hqr with hq hr,
        constructor,
        constructor,
        repeat { assumption }
    end

    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hpq hr,
        cases hpq with hp hq,
        apply or.inl,
        exact hp,
        apply or.inr,
        apply or.inl,
        exact hq,
        apply or.inr,
        apply or.inr,
        exact hr,
        -- <-
        intro h,
        cases h with hp hqr,
        apply or.inl,
        apply or.inl,
        exact hp,
        cases hqr with hq hr,
        apply or.inl,
        apply or.inr,
        exact hq,
        apply or.inr,
        exact hr
    end

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hp hqr,
        cases hqr with hq hr,
        left,
        constructor,
        repeat { assumption },
        right,
        constructor,
        repeat { assumption },
        -- <-
        intro h,
        cases h with hpq hpr,
        cases hpq with hp hq,
        constructor,
        exact hp,
        left,
        exact hq,
        constructor,
        cases hpr with hp hr,
        exact hp,
        cases hpr with hp hr,
        right,
        exact hr
    end

    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hp hqr,
        apply and.intro,
        left,
        exact hp,
        left,
        exact hp,
        cases hqr with hq hr,
        apply and.intro,
        right,
        exact hq,
        right,
        exact hr,
        -- <-
        intro h,
        cases h with hpq hpr,
        cases hpq with hp hq,
        left,
        exact hp,
        cases hpr with hp hr,
        left,
        exact hp,
        right,
        apply and.intro,
        repeat { assumption }
    end

    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        intro hpq,
        cases hpq with hp hq,
        exact (h hp) hq,
        -- <-
        intro h,
        intro hp,
        intro hq,
        have hpq : p ∧ q, from ⟨hp, hq⟩,
        exact h hpq
    end

    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        apply and.intro,
        intro hp,
        have hpq : p ∨ q, from or.inl hp,
        exact h hpq,
        intro hq,
        have hpq : p ∨ q, from or.inr hq,
        exact h hpq,
        -- <-
        intro h,
        intro hpq,
        cases h with h1 h2,
        cases hpq with hp hq,
        exact (h1 hp),
        exact (h2 hq)
    end

    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        apply and.intro,
        intro hp,
        have hpq : p ∨ q, from or.inl hp,
        exact h hpq,
        intro hq,
        have hpq : p ∨ q, from or.inr hq,
        exact h hpq,
        -- <-
        intro h,
        intro hpq,
        cases h with hnp hnq,
        cases hpq with hp hq,
        exact hnp hp,
        exact hnq hq
    end

    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    begin
        intro h,
        intro hpq,
        cases h with hnp hnq,
        cases hpq with hp hq,
        exact hnp hp,
        cases hpq with hp hq,
        exact hnq hq
    end

    example : ¬(p ∧ ¬p) :=
    begin
        intro h,
        cases h with hp hnp,
        exact hnp hp
    end

    example : p ∧ ¬q → ¬(p → q) :=
    begin
        intro h1,
        cases h1 with hp hnq,
        intro h2,
        have hq : q, from h2 hp,
        exact hnq hq
    end

    example : ¬p → (p → q) :=
    begin
        intro hnp,
        intro hp,
        contradiction
    end

    example : (¬p ∨ q) → (p → q) :=
    begin
        intro h,
        intro hp,
        cases h with hnp hq,
        contradiction,
        exact hq
    end

    example : p ∨ false ↔ p :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hp hfalse,
        exact hp,
        contradiction,
        -- <-
        intro hp,
        left,
        exact hp
    end

    example : p ∧ false ↔ false :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases h with hp hfalse,
        exact hfalse,
        -- <-
        intro h,
        contradiction
    end

    example : (p → q) → (¬q → ¬p) :=
    begin
        intro h,
        intro hnq,
        intro hp,
        exact hnq (h hp)
    end
end ch03_ex01

namespace ch03_ex02
    open classical

    variables p q r s : Prop

    example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    begin
        intro h,
        cases (em p) with hp hnp,
        have hrs : r ∨ s, from h hp,
        cases hrs with hr hs,
        left,
        intro hp,
        exact hr,
        right,
        intro hp,
        exact hs,
        left,
        intro hp,
        contradiction
    end

    example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    begin
        intro h,
        cases (em p) with hp hnp,
        right,
        intro hq,
        exact h ⟨hp, hq⟩,
        left,
        exact hnp
    end

    example : ¬(p → q) → p ∧ ¬q :=
    begin
        intro h,
        cases (em p) with hp hnp,
        cases (em q) with hq hnq,
        apply and.intro,
        exact hp,
        have hpimplq : p → q, from
            begin
                intro hp,
                exact hq
            end,
        contradiction,
        apply and.intro,
        exact hp,
        exact hnq,
        have hpimplq : p → q, from
            begin
                intro hp,
                contradiction
            end,
        contradiction
    end

    example : (p → q) → (¬p ∨ q) :=
    begin
        intro h,
        cases (em p) with hp hnp,
        right,
        exact h hp,
        left,
        exact hnp
    end

    example : (¬q → ¬p) → (p → q) :=
    begin
        intro h,
        intro hp,
        cases (em q) with hq hnq,
        exact hq,
        have hnp : ¬ p, from h hnq,
        contradiction
    end

    example : p ∨ ¬p :=
    begin
        exact (em p)
    end

    example : (((p → q) → p) → p) :=
    begin
        intro h1,
        cases (em p) with hp hnp,
        exact hp,
        have hpimplq : p → q, from
            begin
                intro hp,
                contradiction
            end,
        have hp : p, from h1 hpimplq,
        contradiction
    end
end ch03_ex02

namespace ch03_ex03
    variables p : Prop

    example : ¬(p ↔ ¬p) :=
    begin
        intro h,
        have hpimplnp : p → ¬p, from iff.elim_left h,
        have hnpimplp : ¬p → p, from iff.elim_right h,
        have hnp : ¬p, from
            assume hp : p,
            show false, from absurd hp (hpimplnp hp),
        have hp : p, from hnpimplp hnp,
        contradiction
    end
end ch03_ex03

namespace ch04_ex01
    variables (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        apply and.intro,
        intro xx,
        exact (h xx).left,
        intro xx,
        exact (h xx).right,
        -- <-
        intro h,
        intro xx,
        apply and.intro,
        exact h.left xx,
        exact h.right xx
    end

    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    begin
        intro h1,
        intro h2,
        intro xx,
        exact (h1 xx) (h2 xx)
    end

    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    begin
        intro h,
        intro xx,
        cases h with hl hr,
        left,
        exact hl xx,
        right,
        exact hr xx
    end
end ch04_ex01

namespace ch04_ex02
    open classical

    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) :=
    begin
        intro halpha,
        apply iff.intro,
        -- ->
        intro h,
        exact h halpha,
        -- <-
        intro hr,
        intro halpha',
        exact hr
    end

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        cases (em r) with hr hnr,
        right,
        exact hr,
        left,
        intro xx,
        cases (h xx) with hpxx hr,
        exact hpxx,
        contradiction,
        -- <-
        intro h,
        intro xx,
        cases h with hl hr,
        left,
        exact hl xx,
        right,
        exact hr
    end

    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    begin
        apply iff.intro,
        -- ->
        intro h,
        intro hr,
        intro xx,
        exact h xx hr,
        -- <-
        intro h,
        intro xx,
        intro hr,
        exact h hr xx
    end
end ch04_ex02

namespace ch04_ex03
    open classical

    variables (men : Type) (barber : men)
    variable  (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    begin
        cases (em (shaves barber barber)) with h1 h1',
        {
            have h2 : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
            have h3 : shaves barber barber → ¬ shaves barber barber, from iff.mp h2,
            have h4 : ¬ shaves barber barber, from h3 h1,
            contradiction
        },
        {
            have h2 : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
            have h3 : ¬ shaves barber barber → shaves barber barber, from iff.mpr h2,
            have h4 : shaves barber barber, from h3 h1',
            contradiction
        }
    end
end ch04_ex03

namespace ch04_ex04

end ch04_ex04

namespace ch04_ex05
    open classical

    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    example : (∃ x : α, r) → r :=
    sorry
    example : r → (∃ x : α, r) :=
    sorry
    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    sorry
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    sorry

    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    sorry
    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    sorry
    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    sorry
    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    sorry

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    sorry
    example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    sorry
    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    sorry
end ch04_ex05

namespace ch04_ex06
    variables (real : Type) [ordered_ring real]
    variables (log exp : real → real)
    variable  log_exp_eq : ∀ x, log (exp x) = x
    variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
    variable  exp_pos    : ∀ x, exp x > 0
    variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

    -- this ensures the assumptions are available in tactic proofs
    include log_exp_eq exp_log_eq exp_pos exp_add

    example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
    by rw [exp_add, exp_add]

    example (y : real) (h : y > 0)  : exp (log y) = y :=
    exp_log_eq h

    theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
    sorry
end ch04_ex06

namespace ch04_ex07
    #check sub_self

    example (x : ℤ) : x * 0 = 0 :=
    sorry
end ch04_ex07
