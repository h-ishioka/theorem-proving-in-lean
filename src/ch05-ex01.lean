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
    sorry
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    sorry
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    sorry
    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    sorry
    example : ¬(p ∧ ¬p) :=
    sorry
    example : p ∧ ¬q → ¬(p → q) :=
    sorry
    example : ¬p → (p → q) :=
    sorry
    example : (¬p ∨ q) → (p → q) :=
    sorry
    example : p ∨ false ↔ p :=
    sorry
    example : p ∧ false ↔ false :=
    sorry
    example : (p → q) → (¬q → ¬p) :=
    sorry
end ch03_ex01

namespace ch03_ex02
    open classical

    variables p q r s : Prop

    example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    sorry
    example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    sorry
    example : ¬(p → q) → p ∧ ¬q :=
    sorry
    example : (p → q) → (¬p ∨ q) :=
    sorry
    example : (¬q → ¬p) → (p → q) :=
    sorry
    example : p ∨ ¬p :=
    sorry
    example : (((p → q) → p) → p) :=
    sorry
end ch03_ex02

namespace ch03_ex03
    variables p : Prop

    example : ¬(p ↔ ¬p) :=
    sorry
end ch03_ex03

namespace ch04_ex01
    variables (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    sorry
    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    sorry
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    sorry
end ch04_ex01

namespace ch04_ex02
    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) :=
    sorry
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    sorry
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    sorry
end ch04_ex02

namespace ch04_ex03
    variables (men : Type) (barber : men)
    variable  (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    sorry
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
