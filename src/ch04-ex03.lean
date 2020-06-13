/-
3. Consider the “barber paradox,” that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:
-/

open classical

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    or.elim (em (shaves barber barber))
    (
        assume h1 : shaves barber barber,
        have h2 : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
        have h3 : shaves barber barber → ¬ shaves barber barber, from iff.mp h2,
        have h4 : ¬ shaves barber barber, from h3 h1,
        false.elim (h4 h1)
    )
    (
        assume h1 : ¬ shaves barber barber,
        have h2 : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
        have h3 : ¬ shaves barber barber → shaves barber barber, from iff.mpr h2,
        have h4 : shaves barber barber, from h3 h1,
        false.elim (h1 h4)
    )
-- short version
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    (em (shaves barber barber)).elim
    (λ h1, absurd h1 ((iff.mp (h barber)) h1))
    (λ h1, absurd ((iff.mpr (h barber)) h1) h1)
