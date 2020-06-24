/-
7. Prove the theorem below, using only the ring properties of ℤ enumerated in Section 4.2 and the theorem sub_self.
-/

import data.real.nnreal

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
    calc
        x * 0 = x * (x - x) : by rw sub_self x
          ... = x * x - x * x : by rw mul_sub x
          ... = 0 : by rw sub_self (x * x)
