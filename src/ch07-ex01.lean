/-
1. Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with pred 0 = 0), truncated subtraction (with n - m = 0 when m is greater than or equal to n), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.

Since many of these are already defined in Lean’s core library, you should work within a namespace named hide, or something like that, in order to avoid name clashes.
-/
namespace hidden
  namespace nat
    def mul (m n : nat) : nat :=
      nat.rec_on n 0 (λ n mul_m_n, m + mul_m_n)
    #reduce mul 3 6

    def pred (n : nat) : nat :=
      nat.rec_on n 0 (λ n pred_n, n)
    #reduce pred 10

    def sub (m n : nat) : nat :=
      nat.rec_on n m (λ n sub_m_n, pred sub_m_n)
    #reduce sub 5 2
    #reduce sub 2 5

    def exp (m n : nat) : nat :=
      nat.rec_on n 1 (λ n exp_m_n, mul m exp_m_n)
    #reduce exp 2 4

    theorem mul_zero (n : nat) : mul n 0 = 0 := rfl
    theorem zero_mul (n : nat) : mul 0 n = 0 :=
    nat.rec_on n
    (
      show mul 0 0 = 0, from rfl
    )
    (
      assume n,
      assume ih : mul 0 n = 0,
      show mul 0 (nat.succ n) = 0, from
        calc
          mul 0 (nat.succ n) = 0 + (mul 0 n):  rfl
                         ... = 0 + 0 : by rw ih
                         ... = 0 : rfl
    )

    theorem mul_one (n : nat) : mul n 1 = n := rfl
    theorem one_mul (n : nat) : mul 1 n = n :=
    nat.rec_on n
    (
      show mul 1 0 = 0, from rfl
    )
    (
      assume n,
      assume ih : mul 1 n = n,
      show mul 1 (nat.succ n) = nat.succ n, from
        calc
          mul 1 (nat.succ n) = 1 + (mul 1 n) : rfl
                         ... = 1 + n : by rw ih
                         ... = n + 1 : by rw nat.add_comm
                         ... = nat.succ n : rfl
    )

    theorem pred_succ (n : nat) : pred (nat.succ n) = n := rfl

    theorem zero_sub (n : nat) : sub 0 n = 0 :=
    nat.rec_on n
    (
      show sub 0 0 = 0, from rfl
    )
    (
      assume n,
      assume ih : sub 0 n = 0,
      show sub 0 (nat.succ n) = 0, from congr_arg pred ih
    )

    theorem exp_zero (n : nat) : exp n 0 = 1 := rfl
  end nat
end hidden
