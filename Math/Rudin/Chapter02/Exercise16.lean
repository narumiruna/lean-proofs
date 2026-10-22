module

public import Mathlib

/-! # Exercise 2.16 (PDF page 53)
The rational set `2 < q² < 3` is both open and closed, and is bounded.
It is not compact: the continuous square function has no minimum on it.
-/

@[expose] public section
namespace Rudin.Chapter02

def rationalSquareBand : Set ℚ := {q | 2 < q ^ 2 ∧ q ^ 2 < 3}

/-- An irrational square root prevents equality at a rational endpoint. -/
theorem rational_sq_ne_of_irrational_sqrt (q : ℚ) (a : ℝ)
    (ha : Irrational (Real.sqrt a)) : (q : ℝ) ^ 2 ≠ a := by
  intro h
  apply ha.ne_rat |q|
  rw [← h, Real.sqrt_sq_eq_abs, Rat.cast_abs]

theorem rationalSquareBand_isClosed : IsClosed rationalSquareBand := by
  have h2 : ∀ q : ℚ, q ^ 2 ≠ 2 := by
    intro q h
    apply rational_sq_ne_of_irrational_sqrt q 2 irrational_sqrt_two
    exact_mod_cast h
  have h3 : ∀ q : ℚ, q ^ 2 ≠ 3 := by
    intro q h
    apply rational_sq_ne_of_irrational_sqrt q 3 (by
      simpa using Nat.prime_three.irrational_sqrt)
    exact_mod_cast h
  have heq : rationalSquareBand = (fun q : ℚ => q ^ 2) ⁻¹' Set.Icc 2 3 := by
    ext q
    change (2 < q ^ 2 ∧ q ^ 2 < 3) ↔ (2 ≤ q ^ 2 ∧ q ^ 2 ≤ 3)
    exact ⟨fun h => ⟨h.1.le, h.2.le⟩,
      fun h => ⟨lt_of_le_of_ne h.1 (h2 q).symm, lt_of_le_of_ne h.2 (h3 q)⟩⟩
  rw [heq]
  exact isClosed_Icc.preimage (by fun_prop)

theorem rationalSquareBand_isOpen : IsOpen rationalSquareBand :=
  isOpen_Ioo.preimage (continuous_id.pow 2)

theorem rationalSquareBand_isBounded : Bornology.IsBounded rationalSquareBand := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2, fun q hq => ?_⟩
  rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_le]
  have hq' : (2 : ℝ) < (q : ℝ) ^ 2 ∧ (q : ℝ) ^ 2 < 3 := by
    exact_mod_cast hq
  constructor <;> nlinarith [sq_nonneg ((q : ℝ) - 2), sq_nonneg ((q : ℝ) + 2)]

theorem rationalSquareBand_not_isCompact : ¬ IsCompact rationalSquareBand := by
  intro hc
  have hne : rationalSquareBand.Nonempty := by
    refine ⟨3 / 2, ?_⟩
    norm_num [rationalSquareBand]
  have hf : Continuous (fun q : ℚ => (q : ℝ) ^ 2) := by fun_prop
  obtain ⟨q, hq, hmin⟩ := hc.exists_isMinOn hne hf.continuousOn
  have hq' : (2 : ℝ) < (q : ℝ) ^ 2 ∧ (q : ℝ) ^ 2 < 3 := by
    exact_mod_cast hq
  have hs : Real.sqrt 2 < |(q : ℝ)| := by
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsq := sq_abs (q : ℝ)
    have hnon := abs_nonneg (q : ℝ)
    nlinarith [Real.sqrt_nonneg 2]
  obtain ⟨r, hr, hrq⟩ := exists_rat_btwn hs
  have hr0 : (0 : ℝ) < r := (Real.sqrt_nonneg 2).trans_lt hr
  have hrr : (2 : ℝ) < (r : ℝ) ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hrq2 : (r : ℝ) ^ 2 < (q : ℝ) ^ 2 := by
    nlinarith [sq_abs (q : ℝ), abs_nonneg (q : ℝ)]
  have hrE : r ∈ rationalSquareBand := by
    change 2 < r ^ 2 ∧ r ^ 2 < 3
    exact_mod_cast (show (2 : ℝ) < (r : ℝ) ^ 2 ∧ (r : ℝ) ^ 2 < 3 from
      ⟨hrr, hrq2.trans hq'.2⟩)
  exact (not_le_of_gt hrq2) (hmin hrE)

/-- All four conclusions use the usual metric topology on the rationals. -/
theorem exercise16 : IsClosed rationalSquareBand ∧
    Bornology.IsBounded rationalSquareBand ∧ ¬ IsCompact rationalSquareBand ∧
    IsOpen rationalSquareBand :=
  ⟨rationalSquareBand_isClosed, rationalSquareBand_isBounded,
    rationalSquareBand_not_isCompact, rationalSquareBand_isOpen⟩
end Rudin.Chapter02
