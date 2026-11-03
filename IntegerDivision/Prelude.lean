import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace IntegerDivision

/-- Paper Definition 2.2.  `Divides d x` is stated in the paper's factor order:
there is an integer `k` such that `x = k * d`. -/
def Divides (d x : Int) : Prop := ∃ k : Int, x = k * d

/-- Paper Definition 2.2.  Integers are congruent modulo `d` when `d` divides
their difference. -/
def Congruent (a b d : Int) : Prop := Divides d (a - b)

/-- The paper's `sameSign(a,b)` predicate: the product is nonnegative. -/
def SameSign (a b : Int) : Prop := 0 ≤ a * b

/-- Bridge from the paper's factor order to Lean's standard divisibility
relation.  Proof implementations use this lemma explicitly; paper-facing
statements use `Divides`. -/
theorem divides_iff_dvd (d x : Int) : Divides d x ↔ d ∣ x
:= by
  unfold Divides
  exact dvd_iff_exists_eq_mul_left.symm

/-- A sign-case view useful inside proofs.  The public definition remains the
product inequality printed in Section 2. -/
theorem sameSign_iff (a b : Int) :
    SameSign a b ↔
      (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)
:= by
  exact Int.mul_nonneg_iff

/-- A factor of a nonzero integer is itself nonzero. -/
theorem nonzero_of_dvd_nonzero
    {factor value : Int} (hvalue : value ≠ 0) (hdiv : factor ∣ value) :
    factor ≠ 0
:= by
  exact ne_zero_of_dvd_ne_zero hvalue hdiv

end IntegerDivision
