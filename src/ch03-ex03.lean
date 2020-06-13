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
-- short version
example : ¬(p ↔ ¬p) :=
    λ h,
    have hnp : ¬p, from λ hp, absurd hp (h.mp hp),
    absurd (h.mpr hnp) hnp
