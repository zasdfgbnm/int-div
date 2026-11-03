import IntegerDivision.Specification

set_option autoImplicit false

namespace IntegerDivision

/-- Checked boundary observation following Table 1: at `x = 0`,
reconstruction and the strict bound force the candidate pair to be zero. -/
example (d q r : Int) (hd : d ≠ 0)
    (hrec : 0 = d * q + r) (hbound : |r| < |d|) :
    q = 0 ∧ r = 0
:= by
  have horient : RemainderOrientation .T 0 d r := by
    simp [RemainderOrientation, SameSign]
  have hu := eq_of_reconstruction_bound_orientation
    .T 0 d q r hd hrec hbound horient
  simpa [quotient, remainder, Truncating.quot, Truncating.rem] using hu

/-- Checked opening example following Table 1, stated in its remainder-first
form: `(q, r) = (i, 7)` reconstructs `8 * i + 7`; the remainder is valid
exactly for `i ≥ 0`, invalid for every `i ≤ -1`, and first fails at `i = -1`. -/
example (i : Int) :
    let x := 8 * i + 7
    let q := i
    let r := 7
    x = 8 * q + r ∧
    (RemainderOrientation .T x 8 r ↔ 0 ≤ i) ∧
    (i ≤ -1 → ¬ RemainderOrientation .T x 8 r) ∧
    ¬ RemainderOrientation .T (-1) 8 7
:= by
  dsimp
  unfold RemainderOrientation SameSign
  constructor
  · ring
  constructor
  · constructor <;> omega
  constructor <;> omega

/-! ## 2.1 Rounding Semantics, Exactness, and Congruence -/

/-- The profile-specific condition under which division has quotient zero. -/
def ZeroQuotientCondition (ρ : Profile) (a d : Int) : Prop :=
  match ρ with
  | .E => 0 ≤ a ∧ a < |d|
  | .T => |a| < |d|
  | .F => |a| < |d| ∧ SameSign a d
  | .C => |a| < |d| ∧ SameSign a (-d)

/-- Paper Theorem 2.1 (Zero-quotient characterization). -/
theorem zero_quotient_characterization
    (a d : Int) (hd : d ≠ 0) (ρ : Profile) :
    (quotient ρ a d = 0 ↔ remainder ρ a d = a) ∧
    (quotient ρ a d = 0 ↔ ZeroQuotientCondition ρ a d) ∧
    (remainder ρ a d = a ↔ ZeroQuotientCondition ρ a d)
:= by
  have hqr : quotient ρ a d = 0 ↔ remainder ρ a d = a := by
    constructor
    · intro hq
      have hrec := reconstruction ρ a d hd
      rw [hq] at hrec
      omega
    · intro hr
      have hrec := reconstruction ρ a d hd
      rw [hr] at hrec
      have hzero : d * quotient ρ a d = 0 := by omega
      exact (mul_eq_zero.mp hzero).resolve_left hd
  have hqc : quotient ρ a d = 0 ↔ ZeroQuotientCondition ρ a d := by
    constructor
    · intro hq
      have hr := hqr.mp hq
      have hbound := remainder_bound ρ a d hd
      have horient := remainder_orientation ρ a d hd
      cases ρ with
      | E =>
          change 0 ≤ remainder .E a d at horient
          rw [hr] at hbound horient
          exact ⟨horient, by simpa [abs_of_nonneg horient] using hbound⟩
      | T =>
          change |a| < |d|
          simpa [hr] using hbound
      | F =>
          change |a| < |d| ∧ SameSign a d
          change remainder .F a d = a at hr
          rw [hr] at hbound horient
          simpa [hr, RemainderOrientation] using ⟨hbound, horient⟩
      | C =>
          change |a| < |d| ∧ SameSign a (-d)
          change remainder .C a d = a at hr
          rw [hr] at hbound horient
          simpa [hr, RemainderOrientation] using ⟨hbound, horient⟩
    · intro hcondition
      have hbound : |a| < |d| := by
        cases ρ with
        | E =>
            exact (by
              rw [abs_of_nonneg hcondition.1]
              exact hcondition.2)
        | T => exact hcondition
        | F | C => exact hcondition.1
      have horient : RemainderOrientation ρ a d a := by
        cases ρ with
        | E => exact hcondition.1
        | T =>
            change SameSign a a
            exact mul_self_nonneg a
        | F | C => exact hcondition.2
      exact (eq_of_reconstruction_bound_orientation
        ρ a d 0 a hd (by simp) hbound horient).1.symm
  exact ⟨hqr, hqc, hqr.symm.trans hqc⟩

/-- Paper Theorem 2.3 (Exact divisibility). -/
theorem exact_divisibility
    (a d : Int) (hd : d ≠ 0) (ρ : Profile) :
    Divides d a ↔ remainder ρ a d = 0
:= by
  have _hd : d ≠ 0 := hd
  rw [divides_iff_dvd]
  cases ρ with
  | E => exact Int.dvd_iff_emod_eq_zero
  | T => exact Int.dvd_iff_tmod_eq_zero
  | F => exact Int.dvd_iff_fmod_eq_zero
  | C =>
      rw [show remainder .C a d = -Int.fmod (-a) d from
        Ceiling.rem_eq_neg_fmod_neg a d]
      simp only [neg_eq_zero, ← Int.dvd_iff_fmod_eq_zero, Int.dvd_neg]

/-- Paper Theorem 2.4 (Congruence and remainder representatives). -/
theorem congruence_and_remainder_representatives
    (a b d : Int) (hd : d ≠ 0) :
    (∀ ρ : Profile, Congruent a (remainder ρ a d) d) ∧
    (remainder .E a d = remainder .E b d ↔ Congruent a b d) ∧
    (remainder .F a d = remainder .F b d ↔ Congruent a b d) ∧
    (remainder .C a d = remainder .C b d ↔ Congruent a b d) ∧
    (remainder .T a d = remainder .T b d ↔
      Congruent a b d ∧
        (SameSign a b ∨ Divides d a ∨ Divides d b)) ∧
    (Congruent a b d → ¬ Divides d a → ¬ Divides d b →
      0 < a → b < 0 →
      remainder .T a d = remainder .T b d + |d|) ∧
    (Congruent a b d → ¬ Divides d a → ¬ Divides d b →
      a < 0 → 0 < b →
      remainder .T a d = remainder .T b d - |d|)
:= by
  have hrep : ∀ ρ : Profile, Congruent a (remainder ρ a d) d := by
    intro ρ
    unfold Congruent Divides
    refine ⟨quotient ρ a d, ?_⟩
    have hrec := reconstruction ρ a d hd
    linear_combination hrec
  have heq_to_congruent (ρ : Profile) :
      remainder ρ a d = remainder ρ b d → Congruent a b d := by
    intro hr
    unfold Congruent Divides
    refine ⟨quotient ρ a d - quotient ρ b d, ?_⟩
    have ha := reconstruction ρ a d hd
    have hb := reconstruction ρ b d hd
    rw [hr] at ha
    linear_combination ha - hb
  have hcandidate (ρ : Profile) (hcong : Congruent a b d)
      (horient : RemainderOrientation ρ a d (remainder ρ b d)) :
      remainder ρ a d = remainder ρ b d := by
    rcases hcong with ⟨k, hk⟩
    have hb := reconstruction ρ b d hd
    have hrec :
        a = d * (quotient ρ b d + k) + remainder ρ b d := by
      calc
        a = b + d * k := by linear_combination hk
        _ = (d * quotient ρ b d + remainder ρ b d) + d * k := by
          rw [← hb]
        _ = d * (quotient ρ b d + k) + remainder ρ b d := by ring
    exact (eq_of_reconstruction_bound_orientation ρ a d
      (quotient ρ b d + k) (remainder ρ b d) hd hrec
      (remainder_bound ρ b d hd) horient).2.symm
  have hstable (ρ : Profile)
      (hρ : ρ = .E ∨ ρ = .F ∨ ρ = .C) :
      remainder ρ a d = remainder ρ b d ↔ Congruent a b d := by
    constructor
    · exact heq_to_congruent ρ
    · intro hcong
      apply hcandidate ρ hcong
      rcases hρ with rfl | rfl | rfl
      · exact remainder_orientation .E b d hd
      · exact remainder_orientation .F b d hd
      · exact remainder_orientation .C b d hd
  have hdiv_transfer (hcong : Congruent a b d) :
      Divides d a ↔ Divides d b := by
    change Divides d (a - b) at hcong
    have hdvd := (divides_iff_dvd d (a - b)).1 hcong
    simpa only [divides_iff_dvd] using Int.dvd_iff_dvd_of_dvd_sub hdvd
  have hT_same (hcong : Congruent a b d) (hs : SameSign a b) :
      remainder .T a d = remainder .T b d := by
    by_cases hb0 : b = 0
    · subst b
      have hda : Divides d a := by simpa [Congruent] using hcong
      rw [(exact_divisibility a d hd .T).1 hda,
        (exact_divisibility 0 d hd .T).1 ⟨0, by simp⟩]
    · apply hcandidate .T hcong
      have hbOrient := remainder_orientation .T b d hd
      change SameSign (remainder .T b d) a
      apply (sameSign_iff _ _).2
      rcases (sameSign_iff _ _).1 hs with hs | hs
      · left
        refine ⟨?_, hs.1⟩
        rcases (sameSign_iff _ _).1 hbOrient with h | h
        · exact h.1
        · omega
      · right
        refine ⟨?_, hs.1⟩
        rcases (sameSign_iff _ _).1 hbOrient with h | h
        · omega
        · exact h.1
  have hT :
      remainder .T a d = remainder .T b d ↔
        Congruent a b d ∧
          (SameSign a b ∨ Divides d a ∨ Divides d b) := by
    constructor
    · intro hr
      have hcong := heq_to_congruent .T hr
      refine ⟨hcong, ?_⟩
      by_cases hda : Divides d a
      · exact Or.inr (Or.inl hda)
      by_cases hdb : Divides d b
      · exact Or.inr (Or.inr hdb)
      left
      by_contra hs
      have haOrient := remainder_orientation .T a d hd
      have hbOrient := remainder_orientation .T b d hd
      change SameSign (remainder .T a d) a at haOrient
      change SameSign (remainder .T b d) b at hbOrient
      rw [← hr] at hbOrient
      have hr0 : remainder .T a d = 0 := by
        rw [sameSign_iff] at haOrient hbOrient
        have hs' : ¬ ((0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :=
          fun h => hs ((sameSign_iff _ _).2 h)
        rcases haOrient with haOrient | haOrient <;>
          rcases hbOrient with hbOrient | hbOrient <;> omega
      exact hda ((exact_divisibility a d hd .T).2 hr0)
    · rintro ⟨hcong, hs | hda | hdb⟩
      · exact hT_same hcong hs
      · have hdb := (hdiv_transfer hcong).1 hda
        rw [(exact_divisibility a d hd .T).1 hda,
          (exact_divisibility b d hd .T).1 hdb]
      · have hda := (hdiv_transfer hcong).2 hdb
        rw [(exact_divisibility a d hd .T).1 hda,
          (exact_divisibility b d hd .T).1 hdb]
  have hplus_for (x y : Int) :
      Congruent x y d → ¬ Divides d x → ¬ Divides d y →
        0 < x → y < 0 →
        remainder .T x d = remainder .T y d + |d| := by
    intro hcong hndx hndy hx hy
    have hry_ne : remainder .T y d ≠ 0 := by
      intro hry
      exact hndy ((exact_divisibility y d hd .T).2 hry)
    have hry_neg : remainder .T y d < 0 := by
      have hs := remainder_orientation .T y d hd
      change SameSign (remainder .T y d) y at hs
      rcases (sameSign_iff _ _).1 hs with h | h <;> omega
    have hry_bounds := abs_lt.mp (remainder_bound .T y d hd)
    have hdabs : 0 < |d| := abs_pos.mpr hd
    have hcand_pos : 0 < remainder .T y d + |d| := by omega
    have hcand_range : abs (remainder .T y d + |d|) < |d| := by
      rw [abs_of_pos hcand_pos]
      omega
    have hcand_sign :
        RemainderOrientation .T x d (remainder .T y d + |d|) :=
      (sameSign_iff _ _).2 (Or.inl ⟨hcand_pos.le, hx.le⟩)
    rcases hcong with ⟨k, hk⟩
    have habs : |d| = d * Int.sign d := by
      simpa only [mul_comm] using (Int.sign_mul_self_eq_abs d).symm
    have hyrec := reconstruction .T y d hd
    have hcand_rec :
        x = d * (quotient .T y d + k - Int.sign d) +
          (remainder .T y d + |d|) := by
      calc
        x = y + d * k := by linear_combination hk
        _ = (d * quotient .T y d + remainder .T y d) + d * k := by
          rw [← hyrec]
        _ = d * (quotient .T y d + k - Int.sign d) +
            (remainder .T y d + |d|) := by rw [habs]; ring
    exact (eq_of_reconstruction_bound_orientation .T x d
      (quotient .T y d + k - Int.sign d)
      (remainder .T y d + |d|) hd hcand_rec hcand_range hcand_sign).2.symm
  have hplus :
      Congruent a b d → ¬ Divides d a → ¬ Divides d b →
        0 < a → b < 0 →
        remainder .T a d = remainder .T b d + |d| :=
    hplus_for a b
  have hminus :
      Congruent a b d → ¬ Divides d a → ¬ Divides d b →
        a < 0 → 0 < b →
        remainder .T a d = remainder .T b d - |d| := by
    intro hcong hnda hndb ha hb
    have hsymm : Congruent b a d := by
      rcases hcong with ⟨k, hk⟩
      exact ⟨-k, by linear_combination -hk⟩
    have hba := hplus_for b a hsymm hndb hnda hb ha
    omega
  exact ⟨hrep,
    hstable .E (Or.inl rfl),
    hstable .F (Or.inr (Or.inl rfl)),
    hstable .C (Or.inr (Or.inr rfl)),
    hT, hplus, hminus⟩

/-- Checked example following Paper Theorem 2.4. -/
example :
    Congruent 1 (-1) 2 ∧
    remainder .T 1 2 = 1 ∧ remainder .T (-1) 2 = -1
:= by
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  decide

/-! ## 2.2 Distributivity over Addition -/

/-- Checked quotient-addition counterexamples preceding Paper Theorem 2.5. -/
example :
    (quotient .E (1 + 1) 2 = 1 ∧
      quotient .E 1 2 + quotient .E 1 2 = 0) ∧
    (quotient .T (1 + 1) 2 = 1 ∧
      quotient .T 1 2 + quotient .T 1 2 = 0) ∧
    (quotient .F (1 + 1) 2 = 1 ∧
      quotient .F 1 2 + quotient .F 1 2 = 0) ∧
    (quotient .C (1 + 1) 2 = 1 ∧
      quotient .C 1 2 + quotient .C 1 2 = 2)
:= by
  decide

/-- Paper Theorem 2.5 (Addition without carry). -/
theorem addition_without_carry
    (a b d : Int) (hd : d ≠ 0) (ρ : Profile) :
    let u := remainder ρ a d + remainder ρ b d
    quotient ρ (a + b) d = quotient ρ a d + quotient ρ b d ↔
      match ρ with
      | .T => |u| < |d| ∧ SameSign u (a + b)
      | .E | .F | .C => |u| < |d|
:= by
  dsimp
  have ha := reconstruction ρ a d hd
  have hb := reconstruction ρ b d hd
  have hsum :
      a + b = d * (quotient ρ a d + quotient ρ b d) +
        (remainder ρ a d + remainder ρ b d) := by
    linear_combination ha + hb
  constructor
  · intro hq
    have htarget := reconstruction ρ (a + b) d hd
    rw [hq] at htarget
    have hr : remainder ρ (a + b) d =
        remainder ρ a d + remainder ρ b d := by
      omega
    have hbound := remainder_bound ρ (a + b) d hd
    rw [hr] at hbound
    cases ρ with
    | E | F | C => exact hbound
    | T =>
        have horient := remainder_orientation .T (a + b) d hd
        rw [hr] at horient
        exact ⟨hbound, horient⟩
  · intro hcondition
    have hbound :
        |remainder ρ a d + remainder ρ b d| < |d| := by
      cases ρ with
      | E | F | C => exact hcondition
      | T => exact hcondition.1
    have horient : RemainderOrientation ρ (a + b) d
        (remainder ρ a d + remainder ρ b d) := by
      have haOrient := remainder_orientation ρ a d hd
      have hbOrient := remainder_orientation ρ b d hd
      cases ρ with
      | E =>
          change 0 ≤ remainder .E a d + remainder .E b d
          change 0 ≤ remainder .E a d at haOrient
          change 0 ≤ remainder .E b d at hbOrient
          exact add_nonneg haOrient hbOrient
      | T => exact hcondition.2
      | F =>
          change SameSign (remainder .F a d + remainder .F b d) d
          change SameSign (remainder .F a d) d at haOrient
          change SameSign (remainder .F b d) d at hbOrient
          unfold SameSign at haOrient hbOrient ⊢
          simpa only [add_mul] using add_nonneg haOrient hbOrient
      | C =>
          change SameSign (remainder .C a d + remainder .C b d) (-d)
          change SameSign (remainder .C a d) (-d) at haOrient
          change SameSign (remainder .C b d) (-d) at hbOrient
          unfold SameSign at haOrient hbOrient ⊢
          simpa only [add_mul] using add_nonneg haOrient hbOrient
    exact (eq_of_reconstruction_bound_orientation ρ (a + b) d
      (quotient ρ a d + quotient ρ b d)
      (remainder ρ a d + remainder ρ b d) hd hsum hbound horient).1.symm

/-- Paper Theorem 2.6 (Addition with an exactly divisible addend). -/
theorem addition_with_exactly_divisible_addend
    (a b d : Int) (hd : d ≠ 0) (hda : Divides d a) (ρ : Profile) :
    match ρ with
    | .E | .F | .C =>
        quotient ρ (a + b) d = quotient ρ a d + quotient ρ b d ∧
        remainder ρ (a + b) d = remainder ρ b d
    | .T =>
        let quotientIdentity :=
          quotient .T (a + b) d = quotient .T a d + quotient .T b d
        let remainderIdentity :=
          remainder .T (a + b) d = remainder .T b d
        let guard := SameSign (a + b) b ∨ Divides d b
        (quotientIdentity ↔ remainderIdentity) ∧
        (quotientIdentity ↔ guard) ∧
        (remainderIdentity ↔ guard) ∧
        (SameSign a b → quotientIdentity ∧ remainderIdentity)
:= by
  have hda' : d ∣ a := (divides_iff_dvd d a).1 hda
  cases ρ with
  | E =>
      constructor
      · exact Int.add_ediv_of_dvd_left hda'
      · change (a + b) % d = b % d
        simpa [Int.emod_eq_zero_of_dvd hda'] using Int.add_emod a b d
  | F =>
      constructor
      · exact Int.add_fdiv_of_dvd_left hda'
      · simpa [remainder, Floor.rem, Int.fmod_eq_zero_of_dvd hda'] using
          Int.add_fmod a b d
  | C =>
      constructor
      · simp only [quotient, Ceiling.quot]
        simpa only [neg_add_rev] using congrArg Neg.neg
          (Int.add_fdiv_of_dvd_right (Int.dvd_neg.mpr hda'))
      · simpa [remainder, Ceiling.rem_eq_neg_fmod_neg,
          Int.fmod_eq_zero_of_dvd (Int.dvd_neg.mpr hda')] using
          congrArg Neg.neg (Int.add_fmod (-b) (-a) d)
  | T =>
      have hra : remainder .T a d = 0 :=
        (exact_divisibility a d hd .T).1 hda
      have hcong : Congruent (a + b) b d := by
        rcases hda with ⟨k, hk⟩
        exact ⟨k, by linear_combination hk⟩
      have hab := reconstruction .T a d hd
      have hb := reconstruction .T b d hd
      have hsum := reconstruction .T (a + b) d hd
      have hqr :
          (quotient .T (a + b) d = quotient .T a d + quotient .T b d) ↔
            remainder .T (a + b) d = remainder .T b d := by
        constructor <;> intro h
        · have hab0 := hab
          rw [hra] at hab0
          rw [h] at hsum
          linear_combination -hsum + hab0 + hb
        · have hab0 := hab
          rw [hra] at hab0
          rw [h] at hsum
          have hzero : d * (quotient .T (a + b) d -
              (quotient .T a d + quotient .T b d)) = 0 := by
            linear_combination hab0 + hb - hsum
          have := (mul_eq_zero.mp hzero).resolve_left hd
          omega
      have hdivsum : Divides d (a + b) ↔ Divides d b := by
        simpa only [divides_iff_dvd] using Int.dvd_add_right hda'
      have ht := (congruence_and_remainder_representatives
        (a + b) b d hd).2.2.2.2.1
      have hr :
          remainder .T (a + b) d = remainder .T b d ↔
            SameSign (a + b) b ∨ Divides d b := by
        constructor
        · intro hrem
          rcases (ht.1 hrem).2 with hs | hsumdiv | hbdiv
          · exact Or.inl hs
          · exact Or.inr (hdivsum.1 hsumdiv)
          · exact Or.inr hbdiv
        · intro hguard
          refine ht.2 ⟨hcong, ?_⟩
          rcases hguard with hs | hbdiv
          · exact Or.inl hs
          · exact Or.inr (Or.inr hbdiv)
      have hq := hqr.trans hr
      refine ⟨hqr, hq, hr, ?_⟩
      intro hs
      have hguard : SameSign (a + b) b := by
        unfold SameSign at hs ⊢
        simpa only [add_mul] using add_nonneg hs (mul_self_nonneg b)
      exact ⟨hq.2 (Or.inl hguard), hr.2 (Or.inl hguard)⟩

/-- Paper Theorem 2.7 (Addition in a shared-factor window). -/
theorem addition_in_shared_factor_window
    (a b d g : Int) (hd : d ≠ 0)
    (hga : Divides g a) (hgd : Divides g d) (ρ : Profile) :
    g ≠ 0 ∧
      ((match ρ with
          | .E => 0 ≤ b ∧ b < |g|
          | .T => |b| < |g| ∧ SameSign a b
          | .F => |b| < |g| ∧ SameSign b d
          | .C => |b| < |g| ∧ SameSign b (-d)) →
          remainder ρ (a + b) d = remainder ρ a d + b ∧
          quotient ρ (a + b) d = quotient ρ a d)
:= by
  have hga' : g ∣ a := (divides_iff_dvd g a).1 hga
  have hgd' : g ∣ d := (divides_iff_dvd g d).1 hgd
  have hg : g ≠ 0 := nonzero_of_dvd_nonzero hd hgd'
  refine ⟨hg, ?_⟩
  have hGpos : 0 < |g| := abs_pos.mpr hg
  have hG_a : |g| ∣ a := (abs_dvd g a).2 hga'
  have hG_d : |g| ∣ d := (abs_dvd g d).2 hgd'
  have hG_dabs : |g| ∣ |d| := by
    by_cases hd0 : 0 ≤ d
    · simpa [abs_of_nonneg hd0] using hG_d
    · have hneg : |g| ∣ -d := Int.dvd_neg.mpr hG_d
      simpa [abs_of_neg (lt_of_not_ge hd0)] using hneg
  have hbase := reconstruction ρ a d hd
  have hG_mul : |g| ∣ d * quotient ρ a d := dvd_mul_of_dvd_left hG_d _
  have hG_rem : |g| ∣ remainder ρ a d := by
    apply (Int.dvd_add_right hG_mul).mp
    rw [← hbase]
    exact hG_a
  have hrec :
      a + b = d * quotient ρ a d + (remainder ρ a d + b) := by
    calc
      a + b = (d * quotient ρ a d + remainder ρ a d) + b :=
        congrArg (fun x : Int => x + b) hbase
      _ = d * quotient ρ a d + (remainder ρ a d + b) := by ring
  have hnonnegative_window
      (hr0 : 0 ≤ remainder ρ a d) (hb0 : 0 ≤ b) (hbg : |b| < |g|)
      (horient : RemainderOrientation ρ (a + b) d
        (remainder ρ a d + b)) :
      remainder ρ (a + b) d = remainder ρ a d + b ∧
      quotient ρ (a + b) d = quotient ρ a d := by
    have hgap : |g| + remainder ρ a d ≤ |d| :=
      (Int.le_add_iff_lt_of_dvd_sub hGpos
        (Int.dvd_sub hG_dabs hG_rem)).2 (by
          have := (abs_lt.mp (remainder_bound ρ a d hd)).2
          omega)
    have hbound : |remainder ρ a d + b| < |d| := by
      rw [abs_of_nonneg (add_nonneg hr0 hb0)]
      have := (abs_lt.mp hbg).2
      omega
    have hu := eq_of_reconstruction_bound_orientation ρ (a + b) d
      (quotient ρ a d) (remainder ρ a d + b) hd hrec hbound horient
    exact ⟨hu.2.symm, hu.1.symm⟩
  have hnonpositive_window
      (hr0 : remainder ρ a d ≤ 0) (hb0 : b ≤ 0) (hbg : |b| < |g|)
      (horient : RemainderOrientation ρ (a + b) d
        (remainder ρ a d + b)) :
      remainder ρ (a + b) d = remainder ρ a d + b ∧
      quotient ρ (a + b) d = quotient ρ a d := by
    have hgap : |g| + -remainder ρ a d ≤ |d| :=
      (Int.le_add_iff_lt_of_dvd_sub hGpos
        (Int.dvd_sub hG_dabs (Int.dvd_neg.mpr hG_rem))).2 (by
          have := (abs_lt.mp (remainder_bound ρ a d hd)).1
          omega)
    have hbound : |remainder ρ a d + b| < |d| := by
      rw [abs_of_nonpos (add_nonpos hr0 hb0)]
      have := (abs_lt.mp hbg).1
      omega
    have hu := eq_of_reconstruction_bound_orientation ρ (a + b) d
      (quotient ρ a d) (remainder ρ a d + b) hd hrec hbound horient
    exact ⟨hu.2.symm, hu.1.symm⟩
  have ht_nonneg (hx : 0 ≤ a) : 0 ≤ remainder .T a d := by
    by_cases ha0 : a = 0
    · subst a
      rw [(exact_divisibility 0 d hd .T).1 ⟨0, by simp⟩]
    · have hs := remainder_orientation .T a d hd
      change SameSign (remainder .T a d) a at hs
      rcases (sameSign_iff _ _).1 hs with h | h <;> omega
  have ht_nonpos (hx : a ≤ 0) : remainder .T a d ≤ 0 := by
    by_cases ha0 : a = 0
    · subst a
      rw [(exact_divisibility 0 d hd .T).1 ⟨0, by simp⟩]
    · have hs := remainder_orientation .T a d hd
      change SameSign (remainder .T a d) a at hs
      rcases (sameSign_iff _ _).1 hs with h | h <;> omega
  cases ρ with
  | E =>
      rintro ⟨hb0, hbg⟩
      have hr0 : 0 ≤ remainder .E a d := remainder_orientation .E a d hd
      exact hnonnegative_window hr0 hb0
        (by simpa [abs_of_nonneg hb0] using hbg) (add_nonneg hr0 hb0)
  | T =>
      rintro ⟨hbg, hs⟩
      rcases (sameSign_iff _ _).1 hs with hnonneg | hnonpos
      · have hr0 := ht_nonneg hnonneg.1
        apply hnonnegative_window hr0 hnonneg.2 hbg
        exact (sameSign_iff _ _).2 (Or.inl
          ⟨add_nonneg hr0 hnonneg.2, add_nonneg hnonneg.1 hnonneg.2⟩)
      · have hr0 := ht_nonpos hnonpos.1
        apply hnonpositive_window hr0 hnonpos.2 hbg
        exact (sameSign_iff _ _).2 (Or.inr
          ⟨add_nonpos hr0 hnonpos.2, add_nonpos hnonpos.1 hnonpos.2⟩)
  | F =>
      rintro ⟨hbg, hs⟩
      rcases lt_or_gt_of_ne hd with hdneg | hdpos
      · have hr0 : remainder .F a d ≤ 0 := by
          have h := remainder_orientation .F a d hd
          change SameSign (remainder .F a d) d at h
          rcases (sameSign_iff _ _).1 h with h | h <;> omega
        have hb0 : b ≤ 0 := by
          rcases (sameSign_iff _ _).1 hs with h | h <;> omega
        apply hnonpositive_window hr0 hb0 hbg
        exact (sameSign_iff _ _).2
          (Or.inr ⟨add_nonpos hr0 hb0, hdneg.le⟩)
      · have hr0 : 0 ≤ remainder .F a d := by
          have h := remainder_orientation .F a d hd
          change SameSign (remainder .F a d) d at h
          rcases (sameSign_iff _ _).1 h with h | h <;> omega
        have hb0 : 0 ≤ b := by
          rcases (sameSign_iff _ _).1 hs with h | h <;> omega
        apply hnonnegative_window hr0 hb0 hbg
        exact (sameSign_iff _ _).2
          (Or.inl ⟨add_nonneg hr0 hb0, hdpos.le⟩)
  | C =>
      rintro ⟨hbg, hs⟩
      rcases lt_or_gt_of_ne hd with hdneg | hdpos
      · have hr0 : 0 ≤ remainder .C a d := by
          have h := remainder_orientation .C a d hd
          change SameSign (remainder .C a d) (-d) at h
          rcases (sameSign_iff _ _).1 h with h | h <;> omega
        have hb0 : 0 ≤ b := by
          rcases (sameSign_iff _ _).1 hs with h | h <;> omega
        apply hnonnegative_window hr0 hb0 hbg
        exact (sameSign_iff _ _).2
          (Or.inl ⟨add_nonneg hr0 hb0, by omega⟩)
      · have hr0 : remainder .C a d ≤ 0 := by
          have h := remainder_orientation .C a d hd
          change SameSign (remainder .C a d) (-d) at h
          rcases (sameSign_iff _ _).1 h with h | h <;> omega
        have hb0 : b ≤ 0 := by
          rcases (sameSign_iff _ _).1 hs with h | h <;> omega
        apply hnonpositive_window hr0 hb0 hbg
        exact (sameSign_iff _ _).2
          (Or.inr ⟨add_nonpos hr0 hb0, by omega⟩)

/-- The greatest-common-divisor choice following Paper Theorem 2.7 is an
eligible shared factor whose row window contains the window supplied by every
other eligible shared factor. -/
theorem gcd_gives_widest_shared_factor_window
    (a d g : Int) (hd : d ≠ 0)
    (hga : Divides g a) (hgd : Divides g d) (ρ : Profile) :
    let G : Int := Int.gcd a d
    Divides G a ∧ Divides G d ∧ 0 < G ∧
    ∀ b : Int,
      (match ρ with
        | .E => 0 ≤ b ∧ b < |g|
        | .T => |b| < |g| ∧ SameSign a b
        | .F => |b| < |g| ∧ SameSign b d
        | .C => |b| < |g| ∧ SameSign b (-d)) →
      (match ρ with
        | .E => 0 ≤ b ∧ b < |G|
        | .T => |b| < |G| ∧ SameSign a b
        | .F => |b| < |G| ∧ SameSign b d
        | .C => |b| < |G| ∧ SameSign b (-d))
:= by
  have hga' : g ∣ a := (divides_iff_dvd g a).1 hga
  have hgd' : g ∣ d := (divides_iff_dvd g d).1 hgd
  dsimp
  have hG : (0 : Int) < Int.gcd a d := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_right a hd
  have hmag : |g| ≤ |(Int.gcd a d : Int)| := by
    rw [abs_of_pos hG]
    exact Int.le_of_dvd hG ((abs_dvd g (Int.gcd a d : Int)).2
      (Int.dvd_coe_gcd hga' hgd'))
  refine ⟨(divides_iff_dvd _ _).2 (Int.gcd_dvd_left a d),
    (divides_iff_dvd _ _).2 (Int.gcd_dvd_right a d), hG, ?_⟩
  intro b hb
  cases ρ with
  | E => exact ⟨hb.1, lt_of_lt_of_le hb.2 hmag⟩
  | T | F | C => exact ⟨lt_of_lt_of_le hb.1 hmag, hb.2⟩

/-- Paper Theorem 2.8 (Remainder of a sum). -/
theorem remainder_of_sum
    (a b d : Int) (hd : d ≠ 0) (ρ : Profile) :
    match ρ with
    | .E | .F | .C =>
        remainder ρ (a + b) d =
          remainder ρ (remainder ρ a d + remainder ρ b d) d
    | .T =>
        let s := remainder .T a d + remainder .T b d
        (remainder .T (a + b) d = remainder .T s d ↔
          SameSign (a + b) s ∨ Divides d (a + b)) ∧
        (SameSign a b →
          remainder .T (a + b) d = remainder .T s d)
:= by
  cases ρ with
  | E => exact Int.add_emod a b d
  | F => exact Int.add_fmod a b d
  | C =>
      simp only [remainder, Ceiling.rem_eq_neg_fmod_neg]
      simpa only [neg_add_rev, neg_neg] using
        congrArg Neg.neg (Int.add_fmod (-b) (-a) d)
  | T =>
      have ha := reconstruction .T a d hd
      have hb := reconstruction .T b d hd
      have hcong : Congruent (a + b)
          (remainder .T a d + remainder .T b d) d := by
        unfold Congruent Divides
        refine ⟨quotient .T a d + quotient .T b d, ?_⟩
        linear_combination ha + hb
      have ht := (congruence_and_remainder_representatives (a + b)
        (remainder .T a d + remainder .T b d) d hd).2.2.2.2.1
      have hdiv :
          Divides d (remainder .T a d + remainder .T b d) ↔
            Divides d (a + b) := by
        change Divides d ((a + b) -
          (remainder .T a d + remainder .T b d)) at hcong
        have hdvd := (divides_iff_dvd d ((a + b) -
          (remainder .T a d + remainder .T b d))).1 hcong
        simpa only [divides_iff_dvd] using
          (Int.dvd_iff_dvd_of_dvd_sub hdvd).symm
      have hiff :
          remainder .T (a + b) d = remainder .T
              (remainder .T a d + remainder .T b d) d ↔
            SameSign (a + b) (remainder .T a d + remainder .T b d) ∨
              Divides d (a + b) := by
        constructor
        · intro hr
          rcases (ht.1 hr).2 with hs | hsum | hsrem
          · exact Or.inl hs
          · exact Or.inr hsum
          · exact Or.inr (hdiv.1 hsrem)
        · intro hguard
          refine ht.2 ⟨hcong, ?_⟩
          rcases hguard with hs | hsum
          · exact Or.inl hs
          · exact Or.inr (Or.inl hsum)
      refine ⟨hiff, ?_⟩
      intro hs
      apply hiff.2
      left
      have hrem_nonneg (x : Int) (hx : 0 ≤ x) :
          0 ≤ remainder .T x d := by
        by_cases hx0 : x = 0
        · subst x
          rw [(exact_divisibility 0 d hd .T).1 ⟨0, by simp⟩]
        · have h := remainder_orientation .T x d hd
          change SameSign (remainder .T x d) x at h
          rcases (sameSign_iff _ _).1 h with h | h <;> omega
      have hrem_nonpos (x : Int) (hx : x ≤ 0) :
          remainder .T x d ≤ 0 := by
        by_cases hx0 : x = 0
        · subst x
          rw [(exact_divisibility 0 d hd .T).1 ⟨0, by simp⟩]
        · have h := remainder_orientation .T x d hd
          change SameSign (remainder .T x d) x at h
          rcases (sameSign_iff _ _).1 h with h | h <;> omega
      apply (sameSign_iff _ _).2
      rcases (sameSign_iff _ _).1 hs with h | h
      · exact Or.inl ⟨add_nonneg h.1 h.2,
          by have ha0 := hrem_nonneg a h.1
             have hb0 := hrem_nonneg b h.2
             exact add_nonneg ha0 hb0⟩
      · exact Or.inr ⟨add_nonpos h.1 h.2,
          by have ha0 := hrem_nonpos a h.1
             have hb0 := hrem_nonpos b h.2
             exact add_nonpos ha0 hb0⟩

/-- Checked counterexample stated immediately after Paper Theorem 2.8. -/
example :
    remainder .T ((4 : Int) + (-2)) 3 = 2 ∧
    remainder .T
      (remainder .T 4 3 + remainder .T (-2) 3) 3 = -1
:= by
  decide

/-! ## 2.3 Multiplicative Laws -/

/-- Paper Theorem 2.9 (Negating operands).  The three conjuncts are the
divisor, dividend, and simultaneous-negation parts in the paper's order. -/
theorem negating_operands
    (a d : Int) (hd : d ≠ 0) (ρ : Profile) :
    let Q := quotient ρ a d
    let R := remainder ρ a d
    (match ρ with
      | .E | .T =>
          (quotient ρ a (-d), remainder ρ a (-d)) = (-Q, R)
      | .F =>
          (Divides d a →
            (quotient .F a (-d), remainder .F a (-d)) = (-Q, 0)) ∧
          (¬ Divides d a →
            (quotient .F a (-d), remainder .F a (-d)) = (-Q - 1, R - d))
      | .C =>
          (Divides d a →
            (quotient .C a (-d), remainder .C a (-d)) = (-Q, 0)) ∧
          (¬ Divides d a →
            (quotient .C a (-d), remainder .C a (-d)) = (-Q + 1, R + d))) ∧
    (match ρ with
      | .E =>
          (Divides d a →
            (quotient .E (-a) d, remainder .E (-a) d) = (-Q, 0)) ∧
          (¬ Divides d a →
            (quotient .E (-a) d, remainder .E (-a) d) =
              (-Q - Int.sign d, |d| - R))
      | .T =>
          (quotient .T (-a) d, remainder .T (-a) d) = (-Q, -R)
      | .F =>
          (Divides d a →
            (quotient .F (-a) d, remainder .F (-a) d) = (-Q, 0)) ∧
          (¬ Divides d a →
            (quotient .F (-a) d, remainder .F (-a) d) = (-Q - 1, d - R))
      | .C =>
          (Divides d a →
            (quotient .C (-a) d, remainder .C (-a) d) = (-Q, 0)) ∧
          (¬ Divides d a →
            (quotient .C (-a) d, remainder .C (-a) d) = (-Q + 1, -d - R))) ∧
    (match ρ with
      | .E =>
          (Divides d a →
            (quotient .E (-a) (-d), remainder .E (-a) (-d)) = (Q, 0)) ∧
          (¬ Divides d a →
            (quotient .E (-a) (-d), remainder .E (-a) (-d)) =
              (Q + Int.sign d, |d| - R))
      | .T | .F | .C =>
          (quotient ρ (-a) (-d), remainder ρ (-a) (-d)) = (Q, -R))
:= by
  have fmod_neg (x e : Int) (he : e ≠ 0) :
      Int.fmod x (-e) =
        if e ∣ x then 0 else Int.fmod x e - e := by
    rw [Int.fmod_def, Int.fmod_def, Int.fdiv_neg he]
    split <;> rename_i h
    · have hmul := Int.mul_fdiv_cancel_of_dvd h
      linear_combination -hmul
    · ring
  have neg_fmod (x e : Int) (he : e ≠ 0) :
      Int.fmod (-x) e =
        if e ∣ x then 0 else e - Int.fmod x e := by
    rw [Int.fmod_def, Int.fmod_def, Int.neg_fdiv]
    simp only [he, false_or]
    split <;> rename_i h
    · have hmul := Int.mul_fdiv_cancel_of_dvd h
      linear_combination hmul
    · ring
  cases ρ with
  | E =>
      dsimp [quotient, remainder, Euclidean.quot, Euclidean.rem]
      refine ⟨Prod.ext (Int.ediv_neg a d) (Int.emod_neg a d), ?_, ?_⟩
      · constructor
        · intro hdiv
          have hdiv' : d ∣ a := (divides_iff_dvd d a).1 hdiv
          apply Prod.ext
          · exact Int.neg_ediv_of_dvd hdiv'
          · exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hdiv')
        · intro hdiv
          have hdiv' : ¬d ∣ a := hdiv ∘ (divides_iff_dvd d a).2
          apply Prod.ext
          · change (-a) / d = -(a / d) - Int.sign d
            simpa [hdiv'] using (Int.neg_ediv (a := a) (b := d))
          · change (-a) % d = |d| - a % d
            simpa [hdiv'] using (Int.neg_emod (a := a) (b := d))
      · constructor
        · intro hdiv
          have hdiv' : d ∣ a := (divides_iff_dvd d a).1 hdiv
          apply Prod.ext
          · change (-a) / (-d) = a / d
            rw [Int.ediv_neg, Int.neg_ediv_of_dvd hdiv']
            simp
          · change (-a) % (-d) = 0
            rw [Int.emod_neg]
            exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hdiv')
        · intro hdiv
          have hdiv' : ¬d ∣ a := hdiv ∘ (divides_iff_dvd d a).2
          apply Prod.ext
          · change (-a) / (-d) = a / d + Int.sign d
            rw [Int.ediv_neg, Int.neg_ediv]
            simp [hdiv']
            omega
          · change (-a) % (-d) = |d| - a % d
            rw [Int.emod_neg]
            simpa [hdiv'] using (Int.neg_emod (a := a) (b := d))
  | T =>
      simp [quotient, remainder, Truncating.quot, Truncating.rem,
        Int.tdiv_neg, Int.neg_tdiv, Int.tmod_neg, Int.neg_tmod]
  | F =>
      dsimp [quotient, remainder, Floor.quot, Floor.rem]
      refine ⟨?_, ?_, Prod.ext (Int.neg_fdiv_neg a d)
        (Int.neg_fmod_neg a d)⟩
      · constructor
        · intro hdiv
          have hdiv' : d ∣ a := (divides_iff_dvd d a).1 hdiv
          apply Prod.ext
          · simpa [hdiv'] using (Int.fdiv_neg (a := a) hd)
          · simpa [hdiv'] using fmod_neg a d hd
        · intro hdiv
          have hdiv' : ¬d ∣ a := hdiv ∘ (divides_iff_dvd d a).2
          apply Prod.ext
          · simpa [hdiv'] using (Int.fdiv_neg (a := a) hd)
          · simpa [hdiv'] using fmod_neg a d hd
      · constructor
        · intro hdiv
          have hdiv' : d ∣ a := (divides_iff_dvd d a).1 hdiv
          apply Prod.ext
          · simpa [hd, hdiv'] using (Int.neg_fdiv (a := a) (b := d))
          · simpa [hdiv'] using neg_fmod a d hd
        · intro hdiv
          have hdiv' : ¬d ∣ a := hdiv ∘ (divides_iff_dvd d a).2
          apply Prod.ext
          · simpa [hd, hdiv'] using (Int.neg_fdiv (a := a) (b := d))
          · simpa [hdiv'] using neg_fmod a d hd
  | C =>
      simp only [quotient, Ceiling.quot, remainder,
        Ceiling.rem_eq_neg_fmod_neg]
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro hdiv
          have hdiv' : d ∣ a := (divides_iff_dvd d a).1 hdiv
          apply Prod.ext
          · simp only [neg_neg]
            calc
              -Int.fdiv (-a) (-d) = -Int.fdiv a d := by
                rw [Int.neg_fdiv_neg]
              _ = Int.fdiv (-a) d :=
                (Int.neg_fdiv_of_dvd hdiv').symm
          · rw [Int.neg_fmod_neg, neg_neg]
            exact Int.fmod_eq_zero_of_dvd hdiv'
        · intro hdiv
          have hdiv' : ¬d ∣ a := hdiv ∘ (divides_iff_dvd d a).2
          apply Prod.ext
          · simp only [neg_neg]
            rw [Int.neg_fdiv_neg]
            have hq := Int.neg_fdiv (a := a) (b := d)
            simp [hd, hdiv'] at hq
            omega
          · rw [Int.neg_fmod_neg, neg_neg]
            have hr := neg_fmod a d hd
            simp [hdiv'] at hr
            omega
      · constructor
        · intro hdiv
          have hdiv' : d ∣ a := (divides_iff_dvd d a).1 hdiv
          apply Prod.ext
          · simp only [neg_neg]
            exact (Int.neg_fdiv_of_dvd hdiv').symm
          · simp only [neg_neg]
            rw [Int.fmod_eq_zero_of_dvd hdiv']
            simp
        · intro hdiv
          have hdiv' : ¬d ∣ a := hdiv ∘ (divides_iff_dvd d a).2
          apply Prod.ext
          · simp only [neg_neg]
            have hq := Int.neg_fdiv (a := a) (b := d)
            simp [hd, hdiv'] at hq
            omega
          · simp only [neg_neg]
            have hr := neg_fmod a d hd
            simp [hdiv'] at hr
            omega
      · apply Prod.ext
        · simp only [neg_neg]
          simpa using congrArg Neg.neg (Int.neg_fdiv_neg (-a) d)
        · simp only [neg_neg]
          simpa using congrArg Neg.neg (Int.neg_fmod_neg (-a) d)

/-- Paper Theorem 2.10 (Homogeneity under exact division). -/
theorem homogeneity_under_exact_division
    (k b c : Int) (hc : c ≠ 0) (hcb : Divides c b) (ρ : Profile) :
    k * quotient ρ b c = quotient ρ (k * b) c
:= by
  have _hc : c ≠ 0 := hc
  have hcb' : c ∣ b := (divides_iff_dvd c b).1 hcb
  cases ρ with
  | E => exact (Int.mul_ediv_assoc k hcb').symm
  | T => exact (Int.mul_tdiv_assoc k hcb').symm
  | F => exact (Int.mul_fdiv_assoc k hcb').symm
  | C =>
      simpa [quotient, Ceiling.quot, mul_neg, neg_mul] using
        (congrArg Neg.neg
          (Int.mul_fdiv_assoc k (Int.dvd_neg.mpr hcb'))).symm

/-- Paper Theorem 2.11 (Remainder of a product). -/
theorem remainder_of_product
    (a b d : Int) (hd : d ≠ 0) (ρ : Profile) :
    remainder ρ (a * b) d =
      remainder ρ (remainder ρ a d * remainder ρ b d) d
:= by
  cases ρ with
  | E => exact Int.mul_emod a b d
  | T => exact Int.mul_tmod a b d
  | F => exact Int.mul_fmod a b d
  | C =>
      have ha := reconstruction .C a d hd
      have hb := reconstruction .C b d hd
      have hcong : Congruent (a * b)
          (remainder .C a d * remainder .C b d) d := by
        unfold Congruent Divides
        refine ⟨quotient .C a d * b +
          quotient .C b d * remainder .C a d, ?_⟩
        linear_combination b * ha + remainder .C a d * hb
      exact ((congruence_and_remainder_representatives (a * b)
        (remainder .C a d * remainder .C b d) d hd).2.2.2.1).2 hcong

/-- The sign fact explaining why Paper Theorem 2.11 needs no extra
truncating guard. -/
theorem truncating_remainder_product_same_sign
    (a b d : Int) (hd : d ≠ 0) :
    SameSign
      (remainder .T a d * remainder .T b d)
      (a * b)
:= by
  have ha := remainder_orientation .T a d hd
  have hb := remainder_orientation .T b d hd
  change SameSign (remainder .T a d) a at ha
  change SameSign (remainder .T b d) b at hb
  unfold SameSign at ha hb ⊢
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg ha hb

/-- Paper Theorem 2.12 (Common-factor cancellation for remainder). -/
theorem common_factor_cancellation_for_remainder
    (a b g : Int) (hb : b ≠ 0)
    (hga : Divides g a) (hgb : Divides g b) (ρ : Profile) :
    g ≠ 0 ∧
    (Int.sign g = -1 ∨ Int.sign g = 1) ∧
    match ρ with
    | .E =>
        remainder .E a b = |g| * remainder .E
          (Int.sign g * quotient .E a g)
          (Int.sign g * quotient .E b g)
    | .T | .F | .C =>
        remainder ρ a b = g * remainder ρ
          (quotient ρ a g) (quotient ρ b g)
:= by
  have hga' : g ∣ a := (divides_iff_dvd g a).1 hga
  have hgb' : g ∣ b := (divides_iff_dvd g b).1 hgb
  have hg : g ≠ 0 := nonzero_of_dvd_nonzero hb hgb'
  have hsign : Int.sign g = -1 ∨ Int.sign g = 1 := by
    rcases lt_or_gt_of_ne hg with hneg | hpos
    · exact Or.inl (Int.sign_eq_neg_one_of_neg hneg)
    · exact Or.inr (Int.sign_eq_one_of_pos hpos)
  refine ⟨hg, hsign, ?_⟩
  cases ρ with
  | E =>
      change a % b = |g| *
        ((Int.sign g * (a / g)) % (Int.sign g * (b / g)))
      have hscale : |g| * Int.sign g = g := by
        simpa only [mul_comm] using Int.sign_mul_abs g
      have ha : |g| * (Int.sign g * (a / g)) = a := by
        rw [← mul_assoc, hscale, Int.mul_ediv_cancel_of_dvd hga']
      have hb' : |g| * (Int.sign g * (b / g)) = b := by
        rw [← mul_assoc, hscale, Int.mul_ediv_cancel_of_dvd hgb']
      calc
        a % b = (|g| * (Int.sign g * (a / g))) %
            (|g| * (Int.sign g * (b / g))) := by rw [ha, hb']
        _ = |g| * ((Int.sign g * (a / g)) %
            (Int.sign g * (b / g))) :=
          Int.mul_emod_mul_of_pos _ _ (abs_pos.mpr hg)
  | T =>
      change a.tmod b = g * ((a.tdiv g).tmod (b.tdiv g))
      rcases lt_or_gt_of_ne hg with hneg | hpos
      · calc
          a.tmod b = (g * (a.tdiv g)).tmod (g * (b.tdiv g)) := by
            rw [Int.mul_tdiv_cancel_of_dvd hga',
              Int.mul_tdiv_cancel_of_dvd hgb']
          _ = g * ((a.tdiv g).tmod (b.tdiv g)) := by
            have h := Int.mul_tmod_mul_of_pos
              (-(a.tdiv g)) (-(b.tdiv g)) (neg_pos.mpr hneg)
            simpa only [neg_mul_neg, Int.neg_tmod, Int.tmod_neg] using h
      · calc
          a.tmod b = (g * (a.tdiv g)).tmod (g * (b.tdiv g)) := by
            rw [Int.mul_tdiv_cancel_of_dvd hga',
              Int.mul_tdiv_cancel_of_dvd hgb']
          _ = g * ((a.tdiv g).tmod (b.tdiv g)) :=
            Int.mul_tmod_mul_of_pos _ _ hpos
  | F =>
      change a.fmod b = g * ((a.fdiv g).fmod (b.fdiv g))
      rcases lt_or_gt_of_ne hg with hneg | hpos
      · calc
          a.fmod b = (g * (a.fdiv g)).fmod (g * (b.fdiv g)) := by
            rw [Int.mul_fdiv_cancel_of_dvd hga',
              Int.mul_fdiv_cancel_of_dvd hgb']
          _ = g * ((a.fdiv g).fmod (b.fdiv g)) := by
            have h := Int.mul_fmod_mul_of_pos
              (-(a.fdiv g)) (-(b.fdiv g)) (neg_pos.mpr hneg)
            simpa only [neg_mul_neg, Int.neg_fmod_neg] using h
      · calc
          a.fmod b = (g * (a.fdiv g)).fmod (g * (b.fdiv g)) := by
            rw [Int.mul_fdiv_cancel_of_dvd hga',
              Int.mul_fdiv_cancel_of_dvd hgb']
          _ = g * ((a.fdiv g).fmod (b.fdiv g)) :=
            Int.mul_fmod_mul_of_pos _ _ hpos
  | C =>
      let A := quotient .C a g
      let B := quotient .C b g
      have harem : remainder .C a g = 0 :=
        (exact_divisibility a g hg .C).1 hga
      have hbrem : remainder .C b g = 0 :=
        (exact_divisibility b g hg .C).1 hgb
      have ha' : a = g * A := by
        have ha := reconstruction .C a g hg
        rw [harem] at ha
        simpa [A] using ha
      have hb' : b = g * B := by
        have hbrec := reconstruction .C b g hg
        rw [hbrem] at hbrec
        simpa [B] using hbrec
      change Ceiling.rem a b = g * Ceiling.rem A B
      rw [ha', hb', Ceiling.rem_eq_neg_fmod_neg,
        Ceiling.rem_eq_neg_fmod_neg]
      rcases lt_or_gt_of_ne hg with hneg | hpos
      · have h := Int.mul_fmod_mul_of_pos A (-B) (neg_pos.mpr hneg)
        have hflip : A.fmod (-B) = -((-A).fmod B) := by
          simpa only [neg_neg] using Int.neg_fmod_neg (-A) B
        have h' := congrArg Neg.neg h
        rw [hflip] at h'
        simpa only [neg_mul_neg, neg_mul, mul_neg, neg_neg] using h'
      · have h := Int.mul_fmod_mul_of_pos (-A) B hpos
        simpa only [mul_neg, neg_mul] using congrArg Neg.neg h

/-! ## 2.4 Reassociation of Nested Divisions -/

private theorem successive_quotient_formula
    (a b c : Int) (hb : b ≠ 0) (hc : c ≠ 0) (ρ : Profile) :
    match ρ with
    | .E =>
        quotient .E a (b * c) =
          Int.sign b * quotient .E (quotient .E a |b|) c
    | .T =>
        quotient .T a (b * c) = quotient .T (quotient .T a b) c
    | .F | .C =>
        quotient ρ a (b * c) =
          quotient ρ (quotient ρ a (Int.sign c * b)) |c|
:= by
  have ht_normalized (x m n : Int) (hm : 0 < m) (hn : 0 < n) :
      quotient .T x (m * n) = quotient .T (quotient .T x m) n := by
    change x.tdiv (m * n) = (x.tdiv m).tdiv n
    rw [← Int.toNat_of_nonneg hm.le, ← Int.toNat_of_nonneg hn.le]
    induction x using Int.wlog_sign
    case inv => simp
    case w x =>
      simp only [← Int.natCast_mul, ← Int.ofNat_tdiv]
      exact congrArg (fun k : Nat => (k : Int))
        (Nat.div_div_eq_div_mul x m.toNat n.toNat).symm
  have hf_normalized (x m n : Int) (hm : m ≠ 0) (hn : 0 < n) :
      quotient .F x (m * n) = quotient .F (quotient .F x m) n := by
    rcases lt_or_gt_of_ne hm with hmneg | hmpos
    · have hM : 0 < -m := by omega
      have hpos := Int.fdiv_fdiv_eq_fdiv_mul (-x) hM.le hn.le
      have hout : quotient .F x (m * n) =
          quotient .F (-x) ((-m) * n) := by
        change Int.fdiv x (m * n) = Int.fdiv (-x) ((-m) * n)
        have h := Int.neg_fdiv_neg (-x) ((-m) * n)
        rw [show m * n = -((-m) * n) by ring]
        simpa only [neg_neg] using h
      have hin : quotient .F x m = quotient .F (-x) (-m) := by
        change Int.fdiv x m = Int.fdiv (-x) (-m)
        simpa only [neg_neg] using (Int.neg_fdiv_neg (-x) (-m))
      rw [hout, hin]
      exact hpos.symm
    · change Int.fdiv x (m * n) = Int.fdiv (Int.fdiv x m) n
      exact (Int.fdiv_fdiv_eq_fdiv_mul x hmpos.le hn.le).symm
  have hFC (σ : Profile) (hσ : σ = .F ∨ σ = .C) :
      quotient σ a (b * c) =
        quotient σ (quotient σ a (Int.sign c * b)) |c| := by
    have hC : 0 < |c| := abs_pos.mpr hc
    have hs : Int.sign c ≠ 0 := mt Int.eq_zero_of_sign_eq_zero hc
    have hb' : Int.sign c * b ≠ 0 := mul_ne_zero hs hb
    have hprod : (Int.sign c * b) * |c| = b * c := by
      rw [mul_assoc, mul_left_comm, Int.sign_mul_abs]
    rcases hσ with rfl | rfl
    · have h := hf_normalized a (Int.sign c * b) |c| hb' hC
      rw [hprod] at h
      exact h
    · have h := hf_normalized (-a) (Int.sign c * b) |c| hb' hC
      rw [hprod] at h
      simpa only [quotient, Ceiling.quot, Floor.quot, neg_neg] using
        congrArg Neg.neg h
  cases ρ with
  | E =>
      have hsigned : quotient .E a (b * c) =
          Int.sign b * quotient .E (Int.sign b * quotient .E a b) c := by
        rcases lt_or_gt_of_ne hb with hbneg | hbpos
        · have hB : 0 < -b := by omega
          have hprod : b * c = -((-b) * c) := by ring
          have hinner : quotient .E a b = -quotient .E a (-b) := by
            change a / b = -(a / (-b))
            simpa only [neg_neg] using (Int.ediv_neg a (-b))
          change Int.ediv a b = -Int.ediv a (-b) at hinner
          have houter : Int.ediv a (b * c) =
              -Int.ediv a ((-b) * c) := by
            rw [hprod]
            exact Int.ediv_neg a ((-b) * c)
          change Int.ediv a (b * c) =
            Int.sign b * Int.ediv (Int.sign b * Int.ediv a b) c
          rw [houter]
          rw [show Int.ediv a ((-b) * c) =
              Int.ediv (Int.ediv a (-b)) c by
            exact (Int.ediv_ediv_of_nonneg hB.le).symm]
          rw [hinner, Int.sign_eq_neg_one_of_neg hbneg]
          simp
        · rw [Int.sign_eq_one_of_pos hbpos]
          simp only [one_mul]
          change Int.ediv a (b * c) = Int.ediv (Int.ediv a b) c
          exact (Int.ediv_ediv_of_nonneg hbpos.le).symm
      have hinner : Int.sign b * quotient .E a b = quotient .E a |b| := by
        rcases lt_or_gt_of_ne hb with hbneg | hbpos
        · rw [Int.sign_eq_neg_one_of_neg hbneg, abs_of_neg hbneg, neg_one_mul]
          have h := congrArg Prod.fst (negating_operands a b hb .E).1
          simpa using h.symm
        · rw [Int.sign_eq_one_of_pos hbpos, abs_of_pos hbpos, one_mul]
      rw [hsigned, hinner]
  | T =>
      rcases lt_or_gt_of_ne hb with hbneg | hbpos
      · rcases lt_or_gt_of_ne hc with hcneg | hcpos
        · have hpos := ht_normalized a (-b) (-c) (by omega) (by omega)
          rw [show b = -(-b) by ring, show c = -(-c) by ring]
          simpa only [quotient, Truncating.quot, Int.tdiv_neg,
            Int.neg_tdiv, neg_neg, neg_mul_neg] using hpos
        · have hpos := ht_normalized a (-b) c (by omega) hcpos
          rw [show b = -(-b) by ring]
          simpa only [quotient, Truncating.quot, Int.tdiv_neg,
            Int.neg_tdiv, neg_neg, neg_mul] using congrArg Neg.neg hpos
      · rcases lt_or_gt_of_ne hc with hcneg | hcpos
        · have hpos := ht_normalized a b (-c) hbpos (by omega)
          rw [show c = -(-c) by ring]
          simpa only [quotient, Truncating.quot, Int.tdiv_neg,
            neg_neg, mul_neg] using congrArg Neg.neg hpos
        · exact ht_normalized a b c hbpos hcpos
  | F => exact hFC .F (Or.inl rfl)
  | C => exact hFC .C (Or.inr rfl)

/-- Paper Theorem 2.13 (Successive division).  Each row returns the quotient
and remainder formulas together. -/
theorem successive_division
    (a b c : Int) (hb : b ≠ 0) (hc : c ≠ 0) (ρ : Profile) :
    match ρ with
    | .E =>
        quotient .E a (b * c) =
            Int.sign b * quotient .E (quotient .E a |b|) c ∧
        remainder .E a (b * c) =
            remainder .E a |b| +
              |b| * remainder .E (quotient .E a |b|) c
    | .T =>
        quotient .T a (b * c) =
            quotient .T (quotient .T a b) c ∧
        remainder .T a (b * c) =
            remainder .T a b +
              b * remainder .T (quotient .T a b) c
    | .F | .C =>
        quotient ρ a (b * c) =
            quotient ρ (quotient ρ a (Int.sign c * b)) |c| ∧
        remainder ρ a (b * c) =
            remainder ρ a (Int.sign c * b) +
              (Int.sign c * b) *
                remainder ρ (quotient ρ a (Int.sign c * b)) |c|
:= by
  have hbc : b * c ≠ 0 := mul_ne_zero hb hc
  have hq := successive_quotient_formula a b c hb hc ρ
  have hFC (hρ : quotient ρ a (b * c) =
      quotient ρ (quotient ρ a (Int.sign c * b)) |c|) :
      remainder ρ a (b * c) =
        remainder ρ a (Int.sign c * b) +
          (Int.sign c * b) *
            remainder ρ (quotient ρ a (Int.sign c * b)) |c| := by
    have hs : Int.sign c ≠ 0 := mt Int.eq_zero_of_sign_eq_zero hc
    have hm : Int.sign c * b ≠ 0 := mul_ne_zero hs hb
    have hprod : (Int.sign c * b) * |c| = b * c := by
      rw [mul_assoc, mul_left_comm, Int.sign_mul_abs]
    have hp := reconstruction ρ a (b * c) hbc
    have hmrec := reconstruction ρ a (Int.sign c * b) hm
    have hcrec := reconstruction ρ
      (quotient ρ a (Int.sign c * b)) |c| (abs_ne_zero.mpr hc)
    rw [hρ] at hp
    have hcrecScaled :
        (Int.sign c * b) * quotient ρ a (Int.sign c * b) =
          (b * c) * quotient ρ
              (quotient ρ a (Int.sign c * b)) |c| +
            (Int.sign c * b) * remainder ρ
              (quotient ρ a (Int.sign c * b)) |c| := by
      calc
        (Int.sign c * b) * quotient ρ a (Int.sign c * b) =
            (Int.sign c * b) *
              (|c| * quotient ρ
                  (quotient ρ a (Int.sign c * b)) |c| +
                remainder ρ
                  (quotient ρ a (Int.sign c * b)) |c|) :=
          congrArg (fun z : Int => (Int.sign c * b) * z) hcrec
        _ = ((Int.sign c * b) * |c|) * quotient ρ
              (quotient ρ a (Int.sign c * b)) |c| +
            (Int.sign c * b) * remainder ρ
              (quotient ρ a (Int.sign c * b)) |c| := by ring
        _ = (b * c) * quotient ρ
              (quotient ρ a (Int.sign c * b)) |c| +
            (Int.sign c * b) * remainder ρ
              (quotient ρ a (Int.sign c * b)) |c| := by rw [hprod]
    linear_combination -hp + hmrec + hcrecScaled
  cases ρ with
  | E =>
      have hp := reconstruction .E a (b * c) hbc
      have hbrec := reconstruction .E a |b| (abs_ne_zero.mpr hb)
      have hcrec := reconstruction .E (quotient .E a |b|) c hc
      rw [hq] at hp
      have hcoef : b * c *
          (Int.sign b * quotient .E (quotient .E a |b|) c) =
          |b| * c * quotient .E (quotient .E a |b|) c := by
        calc
          b * c * (Int.sign b * quotient .E (quotient .E a |b|) c) =
              (b * Int.sign b) * c *
                quotient .E (quotient .E a |b|) c := by ring
          _ = |b| * c * quotient .E (quotient .E a |b|) c := by
            rw [mul_comm b, Int.sign_mul_self_eq_abs]
      rw [hcoef] at hp
      exact ⟨hq, by linear_combination -hp + hbrec + |b| * hcrec⟩
  | T =>
      have hp := reconstruction .T a (b * c) hbc
      have hbrec := reconstruction .T a b hb
      have hcrec := reconstruction .T (quotient .T a b) c hc
      rw [hq] at hp
      exact ⟨hq, by linear_combination -hp + hbrec + b * hcrec⟩
  | F | C => exact ⟨hq, hFC hq⟩

/-- Checked floor-division example stated after Paper Theorem 2.13. -/
example :
    (quotient .F (-17) (-5), remainder .F (-17) (-5)) = (3, -2) ∧
    (quotient .F 3 3, remainder .F 3 3) = (1, 0) ∧
    (quotient .F (-17) (-15), remainder .F (-17) (-15)) = (1, -2)
:= by
  decide

/-- Paper Theorem 2.14 (Division by an exact quotient). -/
theorem division_by_exact_quotient
    (a b c : Int) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcb : Divides c b) (ρ : Profile) :
    match ρ with
    | .E =>
        quotient .E a (quotient .E b c) =
          quotient .E (a * |c|) (Int.sign c * b)
    | .T | .F | .C =>
        quotient ρ a (quotient ρ b c) = quotient ρ (a * c) b
:= by
  have _hb : b ≠ 0 := hb
  have hcb' : c ∣ b := (divides_iff_dvd c b).1 hcb
  cases ρ with
  | E =>
      change a / (b / c) = (a * |c|) / (Int.sign c * b)
      have hb0 : c * (b / c) = b := Int.mul_ediv_cancel_of_dvd hcb'
      have hden : Int.sign c * b = |c| * (b / c) := by
        calc
          Int.sign c * b = Int.sign c * (c * (b / c)) := by rw [hb0]
          _ = |c| * (b / c) := by
            rw [← mul_assoc, Int.sign_mul_self_eq_abs]
      rw [hden]
      simpa only [mul_comm] using
        (Int.mul_ediv_mul_of_pos a (b / c) (abs_pos.mpr hc)).symm
  | T =>
      change a.tdiv (b.tdiv c) = (a * c).tdiv b
      have hb0 : c * (b.tdiv c) = b :=
        Int.mul_tdiv_cancel_of_dvd hcb'
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have h := Int.mul_tdiv_mul_of_pos
          (-a) (-(b.tdiv c)) (neg_pos.mpr hneg)
        simpa only [neg_mul_neg, Int.neg_tdiv_neg, hb0, mul_comm] using h.symm
      · have h := Int.mul_tdiv_mul_of_pos a (b.tdiv c) hpos
        simpa only [hb0, mul_comm] using h.symm
  | F =>
      change a.fdiv (b.fdiv c) = (a * c).fdiv b
      have hb0 : c * (b.fdiv c) = b :=
        Int.mul_fdiv_cancel_of_dvd hcb'
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have h := Int.mul_fdiv_mul_of_pos
          (-a) (-(b.fdiv c)) (neg_pos.mpr hneg)
        simpa only [neg_mul_neg, Int.neg_fdiv_neg, hb0, mul_comm] using h.symm
      · have h := Int.mul_fdiv_mul_of_pos a (b.fdiv c) hpos
        simpa only [hb0, mul_comm] using h.symm
  | C =>
      let B := quotient .C b c
      have hbrem : remainder .C b c = 0 :=
        (exact_divisibility b c hc .C).1 hcb
      have hb0 : c * B = b := by
        have hbrec := reconstruction .C b c hc
        rw [hbrem] at hbrec
        simpa [B] using hbrec.symm
      change Ceiling.quot a B = Ceiling.quot (a * c) b
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have h := Int.mul_fdiv_mul_of_pos
          a (-B) (neg_pos.mpr hneg)
        have hflip : a.fdiv (-B) = (-a).fdiv B := by
          simpa only [neg_neg] using Int.neg_fdiv_neg (-a) B
        have h' := congrArg Neg.neg h.symm
        rw [hflip] at h'
        simpa only [Ceiling.quot, neg_mul_neg, mul_neg, neg_neg,
          hb0, mul_comm] using h'
      · have h := Int.mul_fdiv_mul_of_pos (-a) B hpos
        simpa only [Ceiling.quot, mul_neg, neg_mul, hb0,
          mul_comm] using congrArg Neg.neg h.symm

/-! ## 2.5 Order and Cross-Multiplication -/

/-- Paper Theorem 2.15 (Eliminating a quotient from a strict inequality).
Every sign row is explicit; no case is hidden in an `else` branch. -/
theorem eliminating_quotient_from_strict_inequality
    (i d D : Int) (hd : d ≠ 0) (ρ : Profile) :
    match ρ with
    | .E =>
        (0 < d → (quotient .E i d < D ↔ i < D * d)) ∧
        (d < 0 → (quotient .E i d < D ↔ (D - 1) * d ≤ i))
    | .T =>
        (0 ≤ i → 0 < d →
          (quotient .T i d < D ↔ i < D * d)) ∧
        (0 ≤ i → d < 0 →
          (quotient .T i d < D ↔ (D - 1) * d ≤ i)) ∧
        (i < 0 → 0 < d →
          (quotient .T i d < D ↔ i ≤ (D - 1) * d)) ∧
        (i < 0 → d < 0 →
          (quotient .T i d < D ↔ D * d < i))
    | .F =>
        (0 < d → (quotient .F i d < D ↔ i < D * d)) ∧
        (d < 0 → (quotient .F i d < D ↔ D * d < i))
    | .C =>
        (0 < d → (quotient .C i d < D ↔ i ≤ (D - 1) * d)) ∧
        (d < 0 → (quotient .C i d < D ↔ (D - 1) * d ≤ i))
:= by
  have _hd : d ≠ 0 := hd
  have ediv_pos (x e K : Int) (he : 0 < e) :
      x / e < K ↔ x < K * e :=
    Int.ediv_lt_iff_lt_mul he
  have neg_ediv_pos (x e K : Int) (he : 0 < e) :
      -(x / e) < K ↔ (1 - K) * e ≤ x := by
    calc
      -(x / e) < K ↔ ¬x / e < 1 - K := by omega
      _ ↔ ¬x < (1 - K) * e := not_congr (ediv_pos x e (1 - K) he)
      _ ↔ (1 - K) * e ≤ x := not_lt
  have ediv_neg (x e K : Int) (he : e < 0) :
      x / e < K ↔ (K - 1) * e ≤ x := by
    calc
      x / e < K ↔ -(x / (-e)) < K := by
        rw [show x / e = -(x / (-e)) by
          simpa only [neg_neg] using Int.ediv_neg x (-e)]
      _ ↔ (1 - K) * (-e) ≤ x := neg_ediv_pos x (-e) K (by omega)
      _ ↔ (K - 1) * e ≤ x := by ring_nf
  cases ρ with
  | E =>
      refine ⟨?_, ?_⟩
      · intro hpos
        exact ediv_pos i d D hpos
      · intro hneg
        exact ediv_neg i d D hneg
  | T =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hi hpos
        rw [show quotient .T i d = i / d by
          exact Int.tdiv_eq_ediv_of_nonneg hi]
        exact ediv_pos i d D hpos
      · intro hi hneg
        rw [show quotient .T i d = i / d by
          exact Int.tdiv_eq_ediv_of_nonneg hi]
        exact ediv_neg i d D hneg
      · intro hi hpos
        rw [show quotient .T i d = -((-i) / d) by
          change i.tdiv d = -((-i) / d)
          calc
            i.tdiv d = -((-i).tdiv d) := by
              simpa only [neg_neg] using Int.neg_tdiv (-i) d
            _ = -((-i) / d) := congrArg Neg.neg
              (Int.tdiv_eq_ediv_of_nonneg (by omega))]
        have h := neg_ediv_pos (-i) d D hpos
        rw [show (1 - D) * d = -((D - 1) * d) by ring] at h
        simpa only [Int.neg_le_neg_iff] using h
      · intro hi hneg
        rw [show quotient .T i d = (-i) / (-d) by
          change i.tdiv d = (-i) / (-d)
          calc
            i.tdiv d = (-i).tdiv (-d) := (Int.neg_tdiv_neg i d).symm
            _ = (-i) / (-d) := Int.tdiv_eq_ediv_of_nonneg (by omega)]
        have h := ediv_pos (-i) (-d) D (by omega)
        simpa only [mul_neg, Int.neg_lt_neg_iff] using h
  | F =>
      refine ⟨?_, ?_⟩
      · intro hpos
        rw [show quotient .F i d = i / d by
          exact Int.fdiv_eq_ediv_of_nonneg i hpos.le]
        exact ediv_pos i d D hpos
      · intro hneg
        rw [show quotient .F i d = (-i) / (-d) by
          change i.fdiv d = (-i) / (-d)
          rw [← Int.neg_fdiv_neg]
          exact Int.fdiv_eq_ediv_of_nonneg (-i) (by omega)]
        have h := ediv_pos (-i) (-d) D (by omega)
        simpa only [mul_neg, Int.neg_lt_neg_iff] using h
  | C =>
      refine ⟨?_, ?_⟩
      · intro hpos
        change -Int.fdiv (-i) d < D ↔ i ≤ (D - 1) * d
        rw [Int.fdiv_eq_ediv_of_nonneg (-i) hpos.le]
        have h := neg_ediv_pos (-i) d D hpos
        rw [show (1 - D) * d = -((D - 1) * d) by ring] at h
        simpa only [Int.neg_le_neg_iff] using h
      · intro hneg
        change -Int.fdiv (-i) d < D ↔ (D - 1) * d ≤ i
        rw [show Int.fdiv (-i) d = i / (-d) by
          calc
            Int.fdiv (-i) d = Int.fdiv i (-d) := by
              simpa only [neg_neg] using Int.neg_fdiv_neg i (-d)
            _ = i / (-d) := Int.fdiv_eq_ediv_of_nonneg i (by omega)]
        have h := neg_ediv_pos i (-d) D (by omega)
        rw [show (1 - D) * (-d) = (D - 1) * d by ring] at h
        exact h
end IntegerDivision
