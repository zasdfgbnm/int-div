import IntegerDivision.Semantics

set_option autoImplicit false

namespace IntegerDivision

/-- The quotient-first column of Table 1, stated literally using rounding of
the exact rational quotient. -/
def QuotientCharacterization (ρ : Profile) (x d q : Int) : Prop :=
  match ρ with
  | .E =>
      (0 < d → q = ⌊(x : ℚ) / (d : ℚ)⌋) ∧
      (d < 0 → q = ⌈(x : ℚ) / (d : ℚ)⌉)
  | .T => q = truncate ((x : ℚ) / (d : ℚ))
  | .F => q = ⌊(x : ℚ) / (d : ℚ)⌋
  | .C => q = ⌈(x : ℚ) / (d : ℚ)⌉

/-- The remainder-orientation column of Table 1. -/
def RemainderOrientation (ρ : Profile) (x d r : Int) : Prop :=
  match ρ with
  | .E => 0 ≤ r
  | .T => SameSign r x
  | .F => SameSign r d
  | .C => SameSign r (-d)

/-- The reconstruction, bound, orientation, and uniqueness common to all four
rows of Table 1.  Only the primitive implementation facts branch by profile. -/
private theorem profile_spec
    (ρ : Profile) (x d : Int) (hd : d ≠ 0) :
    x = d * quotient ρ x d + remainder ρ x d ∧
    |remainder ρ x d| < |d| ∧
    RemainderOrientation ρ x d (remainder ρ x d) ∧
    ∀ q r : Int,
      x = d * q + r →
      |r| < |d| →
      RemainderOrientation ρ x d r →
      q = quotient ρ x d ∧ r = remainder ρ x d
:= by
  cases ρ with
  | E =>
      change
        x = d * Euclidean.quot x d + Euclidean.rem x d ∧
        |Euclidean.rem x d| < |d| ∧
        0 ≤ Euclidean.rem x d ∧ _
      have hrec : x = d * Euclidean.quot x d + Euclidean.rem x d :=
        (Int.mul_ediv_add_emod x d).symm
      have hnonneg : 0 ≤ Euclidean.rem x d := Int.emod_nonneg x hd
      have hlt : Euclidean.rem x d < |d| := Int.emod_lt_abs x hd
      refine ⟨hrec, by rw [abs_of_nonneg hnonneg]; exact hlt, hnonneg, ?_⟩
      intro q r hrec' hbound hr0
      have hu := (Int.ediv_emod_unique''
        (a := x) (b := d) (q := q) (r := r) hd).2
        ⟨by omega, hr0, (abs_lt.mp hbound).2⟩
      exact ⟨hu.1.symm, hu.2.symm⟩
  | T =>
      change
        x = d * Truncating.quot x d + Truncating.rem x d ∧
        |Truncating.rem x d| < |d| ∧
        SameSign (Truncating.rem x d) x ∧ _
      have hrec : x = d * Truncating.quot x d + Truncating.rem x d :=
        (Int.mul_tdiv_add_tmod x d).symm
      have hbound : |Truncating.rem x d| < |d| := by
        rw [Truncating.rem, Int.abs_eq_natAbs, Int.abs_eq_natAbs,
          Int.ofNat_lt, Int.natAbs_tmod]
        exact Nat.mod_lt _ (Int.natAbs_pos.mpr hd)
      have horient : SameSign (Truncating.rem x d) x := by
        apply (sameSign_iff _ _).2
        by_cases hx : 0 ≤ x
        · left
          exact ⟨by simpa [Truncating.rem] using Int.tmod_nonneg d hx, hx⟩
        · right
          have h := Int.tmod_nonneg d (show 0 ≤ -x by omega)
          rw [Int.neg_tmod] at h
          exact ⟨by simpa [Truncating.rem] using
            (show Int.tmod x d ≤ 0 by omega), by omega⟩
      refine ⟨hrec, hbound, horient, ?_⟩
      intro q r hrec' hrange hsign
      have ⟨hlower, hupper⟩ := abs_lt.mp hrange
      rw [Int.abs_eq_natAbs] at hlower hupper
      by_cases hx0 : x = 0
      · rw [hx0] at hrec' ⊢
        by_cases hr0 : 0 ≤ r
        · have hu := (Int.tdiv_tmod_unique
            (a := 0) (b := d) (q := q) (r := r) (by simp) hd).2
            ⟨by omega, hr0, hupper⟩
          exact ⟨hu.1.symm, hu.2.symm⟩
        · have hu := (Int.tdiv_tmod_unique'
            (a := 0) (b := d) (q := q) (r := r) (by simp) hd).2
            ⟨by omega, hlower, by omega⟩
          exact ⟨hu.1.symm, hu.2.symm⟩
      · by_cases hx : 0 < x
        · have hr0 : 0 ≤ r := by
            rcases (sameSign_iff _ _).1 hsign with h | h
            · exact h.1
            · omega
          have hu := (Int.tdiv_tmod_unique
            (a := x) (b := d) (q := q) (r := r) hx.le hd).2
            ⟨by omega, hr0, hupper⟩
          exact ⟨hu.1.symm, hu.2.symm⟩
        · have hx' : x < 0 := by omega
          have hr0 : r ≤ 0 := by
            rcases (sameSign_iff _ _).1 hsign with h | h
            · omega
            · exact h.1
          have hu := (Int.tdiv_tmod_unique'
            (a := x) (b := d) (q := q) (r := r) hx'.le hd).2
            ⟨by omega, hlower, hr0⟩
          exact ⟨hu.1.symm, hu.2.symm⟩
  | F =>
      change
        x = d * Floor.quot x d + Floor.rem x d ∧
        |Floor.rem x d| < |d| ∧
        SameSign (Floor.rem x d) d ∧ _
      have hrec : x = d * Floor.quot x d + Floor.rem x d :=
        (Int.mul_fdiv_add_fmod x d).symm
      by_cases hpos : 0 < d
      · have hcanon := (Int.fdiv_fmod_unique
          (a := x) (b := d) (q := Int.fdiv x d) (r := Int.fmod x d) hpos).1
          ⟨rfl, rfl⟩
        have hbound : |Floor.rem x d| < |d| := by
          change |Int.fmod x d| < |d|
          rw [abs_of_nonneg hcanon.2.1, abs_of_pos hpos]
          exact hcanon.2.2
        have horient : SameSign (Floor.rem x d) d :=
          (sameSign_iff _ _).2 (Or.inl ⟨hcanon.2.1, hpos.le⟩)
        refine ⟨hrec, hbound, horient, ?_⟩
        intro q r hrec' hrange hsign
        have hr0 : 0 ≤ r := by
          rcases (sameSign_iff _ _).1 hsign with h | h
          · exact h.1
          · omega
        have hrd : r < d := by
          have := (abs_lt.mp hrange).2
          simpa [abs_of_pos hpos] using this
        have hu := (Int.fdiv_fmod_unique
          (a := x) (b := d) (q := q) (r := r) hpos).2
          ⟨by omega, hr0, hrd⟩
        exact ⟨hu.1.symm, hu.2.symm⟩
      · have hneg : d < 0 := by omega
        have hcanon := (Int.fdiv_fmod_unique'
          (a := x) (b := d) (q := Int.fdiv x d)
          (r := Int.fmod x d) hneg).1 ⟨rfl, rfl⟩
        have hbound : |Floor.rem x d| < |d| := by
          change |Int.fmod x d| < |d|
          rw [abs_of_nonpos hcanon.2.2, abs_of_neg hneg]
          omega
        have horient : SameSign (Floor.rem x d) d :=
          (sameSign_iff _ _).2 (Or.inr ⟨hcanon.2.2, hneg.le⟩)
        refine ⟨hrec, hbound, horient, ?_⟩
        intro q r hrec' hrange hsign
        have hr0 : r ≤ 0 := by
          rcases (sameSign_iff _ _).1 hsign with h | h
          · omega
          · exact h.1
        have hrd : d < r := by
          simpa [abs_of_neg hneg] using (abs_lt.mp hrange).1
        have hu := (Int.fdiv_fmod_unique'
          (a := x) (b := d) (q := q) (r := r) hneg).2
          ⟨by omega, hrd, hr0⟩
        exact ⟨hu.1.symm, hu.2.symm⟩
  | C =>
      change
        x = d * Ceiling.quot x d + Ceiling.rem x d ∧
        |Ceiling.rem x d| < |d| ∧
        SameSign (Ceiling.rem x d) (-d) ∧ _
      have hf := profile_spec .F (-x) d hd
      have hq : Ceiling.quot x d = -quotient .F (-x) d := rfl
      have hr : Ceiling.rem x d = -remainder .F (-x) d :=
        Ceiling.rem_eq_neg_fmod_neg x d
      have hrec : x = d * Ceiling.quot x d + Ceiling.rem x d := by
        simp [Ceiling.rem]
      have horient : SameSign (Ceiling.rem x d) (-d) := by
        rw [hr]
        apply (sameSign_iff _ _).2
        rcases (sameSign_iff _ _).1 hf.2.2.1 with h | h
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      refine ⟨hrec, by simpa [hr] using hf.2.1, horient, ?_⟩
      intro q r hrec' hrange hsign
      have hrecNeg : -x = d * (-q) + (-r) := by
        calc
          -x = -(d * q + r) := by rw [← hrec']
          _ = d * (-q) + (-r) := by ring
      have hsignFloor : RemainderOrientation .F (-x) d (-r) := by
        apply (sameSign_iff _ _).2
        rcases (sameSign_iff _ _).1 hsign with h | h
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      have hu := hf.2.2.2 (-q) (-r) hrecNeg (by simpa using hrange) hsignFloor
      constructor
      · change q = Ceiling.quot x d
        rw [hq]
        omega
      · change r = Ceiling.rem x d
        rw [hr]
        omega
termination_by
  match ρ with
  | .C => 1
  | _ => 0
decreasing_by simp_wf

/-- Table 1: under reconstruction and the common strict remainder bound, the
quotient-first characterization is equivalent to the remainder orientation. -/
theorem quotient_remainder_profiles
    (ρ : Profile) (x d : Int) (hd : d ≠ 0) :
    QuotientCharacterization ρ x d (quotient ρ x d) ∧
    x = d * quotient ρ x d + remainder ρ x d ∧
    |remainder ρ x d| < |d| ∧
    RemainderOrientation ρ x d (remainder ρ x d) ∧
    (∀ q r : Int,
      x = d * q + r →
      |r| < |d| →
      (QuotientCharacterization ρ x d q ↔
        RemainderOrientation ρ x d r)) ∧
    (∀ q r : Int,
      x = d * q + r →
      |r| < |d| →
      RemainderOrientation ρ x d r →
      q = quotient ρ x d ∧ r = remainder ρ x d)
:= by
  have hspec := profile_spec ρ x d hd
  have hquot : QuotientCharacterization ρ x d (quotient ρ x d) := by
    cases ρ with
    | E =>
        constructor
        · intro hpos
          have hsign : RemainderOrientation .F x d (remainder .E x d) :=
            (sameSign_iff _ _).2 (Or.inl ⟨hspec.2.2.1, hpos.le⟩)
          exact ((profile_spec .F x d hd).2.2.2
            (quotient .E x d) (remainder .E x d)
            hspec.1 hspec.2.1 hsign).1.trans (Floor.quot_eq_floor x d hd)
        · intro hneg
          have hsign : RemainderOrientation .C x d (remainder .E x d) :=
            (sameSign_iff _ _).2 (Or.inl ⟨hspec.2.2.1, by omega⟩)
          exact ((profile_spec .C x d hd).2.2.2
            (quotient .E x d) (remainder .E x d)
            hspec.1 hspec.2.1 hsign).1.trans (Ceiling.quot_eq_ceil x d hd)
    | T => exact Truncating.quot_eq_truncate x d hd
    | F => exact Floor.quot_eq_floor x d hd
    | C => exact Ceiling.quot_eq_ceil x d hd
  refine ⟨hquot, hspec.1, hspec.2.1, hspec.2.2.1, ?_, hspec.2.2.2⟩
  intro q r hrec hbound
  constructor
  · intro hqchar
    have hq : q = quotient ρ x d := by
      cases ρ with
      | E =>
          rcases lt_or_gt_of_ne hd with hneg | hpos
          · exact (hqchar.2 hneg).trans (hquot.2 hneg).symm
          · exact (hqchar.1 hpos).trans (hquot.1 hpos).symm
      | T | F | C => exact hqchar.trans hquot.symm
    have hr : r = remainder ρ x d := by
      rw [hq] at hrec
      have hactual := hspec.1
      omega
    simpa [hr] using hspec.2.2.1
  · intro horient
    have hu := hspec.2.2.2 q r hrec hbound horient
    rw [hu.1]
    exact hquot

theorem reconstruction
    (ρ : Profile) (x d : Int) (hd : d ≠ 0) :
    x = d * quotient ρ x d + remainder ρ x d
:= by
  exact (quotient_remainder_profiles ρ x d hd).2.1

theorem remainder_bound
    (ρ : Profile) (x d : Int) (hd : d ≠ 0) :
    |remainder ρ x d| < |d|
:= by
  exact (quotient_remainder_profiles ρ x d hd).2.2.1

theorem remainder_orientation
    (ρ : Profile) (x d : Int) (hd : d ≠ 0) :
    RemainderOrientation ρ x d (remainder ρ x d)
:= by
  exact (quotient_remainder_profiles ρ x d hd).2.2.2.1

theorem eq_of_reconstruction_bound_orientation
    (ρ : Profile) (x d q r : Int) (hd : d ≠ 0)
    (hrec : x = d * q + r) (hbound : |r| < |d|)
    (horient : RemainderOrientation ρ x d r) :
    q = quotient ρ x d ∧ r = remainder ρ x d
:= by
  exact (quotient_remainder_profiles ρ x d hd).2.2.2.2.2
    q r hrec hbound horient

end IntegerDivision
