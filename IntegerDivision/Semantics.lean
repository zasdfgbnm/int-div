import IntegerDivision.Prelude
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

namespace IntegerDivision

/-- The four division profiles quantified over throughout Section 2. -/
inductive Profile where
  | E
  | T
  | F
  | C
  deriving DecidableEq, Repr

/-- Truncation toward zero of an exact rational value, as used in Table 1. -/
def truncate (q : ℚ) : Int := if 0 ≤ q then ⌊q⌋ else ⌈q⌉

private theorem floor_exact_quotient (a d : Int) (hd : d ≠ 0) :
    ⌊(a : ℚ) / (d : ℚ)⌋ = Int.fdiv a d
:= by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hn : (d.natAbs : Int) = -d := by omega
    have hnq : (d.natAbs : ℚ) = -(d : ℚ) := by
      norm_num [Nat.cast_natAbs,
        abs_of_neg (show (d : ℚ) < 0 by exact_mod_cast hneg)]
    have hr :
        (a : ℚ) / (d : ℚ) = ((-a : Int) : ℚ) / (d.natAbs : ℚ) := by
      rw [hnq]
      push_cast
      ring
    rw [hr, Rat.floor_intCast_div_natCast, hn]
    calc
      (-a) / (-d) = Int.fdiv (-a) (-d) :=
        (Int.fdiv_eq_ediv_of_nonneg (-a) (by omega)).symm
      _ = Int.fdiv a d := Int.neg_fdiv_neg a d
  · have hn : (d.natAbs : Int) = d := by omega
    have hnq : (d.natAbs : ℚ) = (d : ℚ) := by
      norm_num [Nat.cast_natAbs,
        abs_of_pos (show (0 : ℚ) < d by exact_mod_cast hpos)]
    have hr : (a : ℚ) / (d : ℚ) = (a : ℚ) / (d.natAbs : ℚ) := by
      rw [hnq]
    rw [hr, Rat.floor_intCast_div_natCast, hn]
    symm
    exact Int.fdiv_eq_ediv_of_nonneg a hpos.le

private theorem ceil_exact_quotient (a d : Int) (hd : d ≠ 0) :
    ⌈(a : ℚ) / (d : ℚ)⌉ = -Int.fdiv (-a) d
:= by
  have hr :
      ((a : ℚ) / (d : ℚ)) = -(((-a : Int) : ℚ) / (d : ℚ)) := by
    push_cast
    ring
  rw [hr, Int.ceil_neg]
  exact congrArg Neg.neg (floor_exact_quotient (-a) d hd)

private theorem tdiv_eq_fdiv_of_nonnegative_of_positive
    (a d : Int) (ha : 0 ≤ a) (hd : 0 < d) :
    Int.tdiv a d = Int.fdiv a d
:= by
  exact (Int.fdiv_eq_tdiv_of_nonneg ha hd.le).symm

private theorem truncate_exact_quotient (a d : Int) (hd : d ≠ 0) :
    truncate ((a : ℚ) / (d : ℚ)) = Int.tdiv a d
:= by
  unfold truncate
  by_cases hq : 0 ≤ (a : ℚ) / (d : ℚ)
  · rw [if_pos hq, floor_exact_quotient a d hd]
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have ha : a ≤ 0 := by
        have hdq : (d : ℚ) < 0 := by exact_mod_cast hneg
        rw [div_nonneg_iff] at hq
        rcases hq with h | h
        · exact False.elim ((not_lt_of_ge h.2) hdq)
        · exact_mod_cast h.1
      have hbase := tdiv_eq_fdiv_of_nonnegative_of_positive
        (-a) (-d) (by omega) (by omega)
      calc
        Int.fdiv a d = Int.fdiv (-a) (-d) := (Int.neg_fdiv_neg a d).symm
        _ = Int.tdiv (-a) (-d) := hbase.symm
        _ = Int.tdiv a d := by simp [Int.neg_tdiv, Int.tdiv_neg]
    · have ha : 0 ≤ a := by
        have hdq : (0 : ℚ) < d := by exact_mod_cast hpos
        rw [div_nonneg_iff] at hq
        rcases hq with h | h
        · exact_mod_cast h.1
        · exact False.elim ((not_lt_of_ge h.2) hdq)
      exact (tdiv_eq_fdiv_of_nonnegative_of_positive a d ha hpos).symm
  · rw [if_neg hq, ceil_exact_quotient a d hd]
    have hqneg : (a : ℚ) / (d : ℚ) < 0 := lt_of_not_ge hq
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have ha : 0 < a := by
        have hdq : (d : ℚ) < 0 := by exact_mod_cast hneg
        rw [div_neg_iff] at hqneg
        rcases hqneg with h | h
        · exact_mod_cast h.1
        · exact False.elim ((not_lt_of_ge hdq.le) h.2)
      have hbase := tdiv_eq_fdiv_of_nonnegative_of_positive
        a (-d) ha.le (by omega)
      have hf : Int.fdiv (-a) d = Int.fdiv a (-d) := by
        simpa only [neg_neg] using Int.neg_fdiv_neg a (-d)
      rw [hf, ← hbase, Int.tdiv_neg]
      ring
    · have ha : a < 0 := by
        have hdq : (0 : ℚ) < d := by exact_mod_cast hpos
        rw [div_neg_iff] at hqneg
        rcases hqneg with h | h
        · exact False.elim ((not_lt_of_ge hdq.le) h.2)
        · exact_mod_cast h.1
      have hbase := tdiv_eq_fdiv_of_nonnegative_of_positive
        (-a) d (by omega) hpos
      rw [← hbase, Int.neg_tdiv]
      ring

namespace Euclidean

def quot (a b : Int) : Int := Int.ediv a b
/-- The Euclidean remainder. -/
def rem (a b : Int) : Int := Int.emod a b

/-- Euclidean residuals occupy the sign-independent half-open cell. -/
def canonical (_x d r : Int) : Prop := 0 ≤ r ∧ r < |d|

@[simp] theorem quot_eq (a b : Int) : quot a b = a / b
:= by
  rfl

@[simp] theorem rem_eq (a b : Int) : rem a b = a % b
:= by
  rfl

end Euclidean

namespace Truncating

def quot (a b : Int) : Int := Int.tdiv a b
/-- The remainder induced by truncating division. -/
def rem (a b : Int) : Int := Int.tmod a b

/-- Truncating residuals are oriented by the dividend. -/
def canonical (x d r : Int) : Prop := |r| < |d| ∧ SameSign r x

@[simp] theorem quot_eq (a b : Int) : quot a b = Int.tdiv a b
:= by
  rfl

@[simp] theorem rem_eq (a b : Int) : rem a b = Int.tmod a b
:= by
  rfl

/-- The truncating quotient is truncation toward zero of the exact rational
quotient. -/
theorem quot_eq_truncate (a d : Int) (hd : d ≠ 0) :
    quot a d = truncate ((a : ℚ) / (d : ℚ))
:= by
  exact (truncate_exact_quotient a d hd).symm

end Truncating

namespace Floor

def quot (a b : Int) : Int := Int.fdiv a b
/-- The remainder induced by flooring division. -/
def rem (a b : Int) : Int := Int.fmod a b

/-- Floor residuals are oriented by the divisor. -/
def canonical (_x d r : Int) : Prop := |r| < |d| ∧ SameSign r d

@[simp] theorem quot_eq (a b : Int) : quot a b = Int.fdiv a b
:= by
  rfl

@[simp] theorem rem_eq (a b : Int) : rem a b = Int.fmod a b
:= by
  rfl

/-- The floor quotient is the floor of the exact rational quotient. -/
theorem quot_eq_floor (a d : Int) (hd : d ≠ 0) :
    quot a d = ⌊(a : ℚ) / (d : ℚ)⌋
:= by
  exact (floor_exact_quotient a d hd).symm

end Floor

namespace Ceiling

def quot (a b : Int) : Int := -Int.fdiv (-a) b
/-- The remainder induced by ceiling division. -/
def rem (a b : Int) : Int := a - b * quot a b

/-- Ceiling residuals are oriented opposite to the divisor. -/
def canonical (_x d r : Int) : Prop := |r| < |d| ∧ SameSign r (-d)

@[simp] theorem quot_eq (a b : Int) : quot a b = -Int.fdiv (-a) b
:= by
  rfl

/-- The ceiling quotient is the ceiling of the exact rational quotient. -/
theorem quot_eq_ceil (a d : Int) (hd : d ≠ 0) :
    quot a d = ⌈(a : ℚ) / (d : ℚ)⌉
:= by
  exact (ceil_exact_quotient a d hd).symm

theorem rem_eq_neg_fmod_neg (a b : Int) :
    rem a b = -Int.fmod (-a) b
:= by
  rw [rem, quot, Int.fmod_def]
  ring

end Ceiling

/-- The paper's profile-indexed quotient `a /ρ d`. -/
def quotient : Profile → Int → Int → Int
  | .E => Euclidean.quot
  | .T => Truncating.quot
  | .F => Floor.quot
  | .C => Ceiling.quot

/-- The paper's profile-indexed remainder `a %ρ d`. -/
def remainder : Profile → Int → Int → Int
  | .E => Euclidean.rem
  | .T => Truncating.rem
  | .F => Floor.rem
  | .C => Ceiling.rem

end IntegerDivision
