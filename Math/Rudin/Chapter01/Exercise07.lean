module

public import Math.Rudin.Chapter01.Exercise06

/-!
# R01E07: logarithm existence by a supremum

Source: Rudin, Third Edition, book page 22 (PDF page 31).
All powers below use the supremum construction in Exercise 6. The source
inequality in (a) is non-strict. Positive integers are represented by positive
natural numbers. Parts (d) and (e) give a positive threshold and hold for every
natural number above it. Existence uses the nonempty, bounded set `A` and the
two perturbation results, not a pre-existing logarithm.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- Part (a), strengthened to include `n = 0`. -/
theorem exercise07_a (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (n : ℝ) * (b - 1) ≤ b ^ n - 1 := by
  have h := one_add_mul_le_pow (a := b - 1) (by linarith) n
  simp only [add_sub_cancel] at h
  linarith

/-- Part (b): apply (a) to the positive `n`th root of the base. -/
theorem exercise07_b (b : ℝ) (hb : 1 < b) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * (exercise06_realPower b hb (1 / (n : ℝ)) - 1) ≤ b - 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 1 < exercise06_realPower b hb (1 / (n : ℝ)) := by
    rw [exercise06_realPower_eq_rpow]
    exact Real.one_lt_rpow hb (one_div_pos.mpr hnR)
  have h := exercise07_a _ hr n
  have hp : exercise06_realPower b hb (1 / (n : ℝ)) ^ n = b := by
    rw [exercise06_realPower_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by linarith : 0 ≤ b)]
    simp [ne_of_gt hnR]
  rwa [hp] at h

/-- Part (c): the explicit bound on the positive integer `n`. -/
theorem exercise07_c (b : ℝ) (hb : 1 < b) (t : ℝ) (ht : 1 < t)
    (n : ℕ) (hn : 0 < n) (hlarge : (b - 1) / (t - 1) < (n : ℝ)) :
    exercise06_realPower b hb (1 / (n : ℝ)) < t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := exercise07_b b hb n hn
  have htR : 0 < t - 1 := by linarith
  have hh := (div_lt_iff₀ htR).mp hlarge
  nlinarith

/-- Positivity of the powers constructed in Exercise 6. -/
theorem exercise07_power_pos (b : ℝ) (hb : 1 < b) (w : ℝ) :
    0 < exercise06_realPower b hb w := by
  rw [exercise06_realPower_eq_rpow]
  exact Real.rpow_pos_of_pos (by linarith) _

/-- Strict monotonicity of the constructed real powers. -/
theorem exercise07_power_strictMono (b : ℝ) (hb : 1 < b) :
    StrictMono (exercise06_realPower b hb) := by
  intro w z hwz
  simp only [exercise06_realPower_eq_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt hb hwz

/-- Part (d): use (c) with `t = y / b^w`, which equals `y * b^(-w)`. -/
theorem exercise07_d (b : ℝ) (hb : 1 < b) (y w : ℝ)
    (hw : exercise06_realPower b hb w < y) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      exercise06_realPower b hb (w + 1 / (n : ℝ)) < y := by
  have hp := exercise07_power_pos b hb w
  have ht : 1 < y / exercise06_realPower b hb w := by
    apply (lt_div_iff₀ hp).mpr
    simpa using hw
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - 1) / (y / exercise06_realPower b hb w - 1))
  refine ⟨max N 1, by omega, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hlarge : (b - 1) / (y / exercise06_realPower b hb w - 1) < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast (show N ≤ n by omega))
  have hr := exercise07_c b hb _ ht n hnpos hlarge
  rw [exercise06_d]
  simpa [mul_comm] using (lt_div_iff₀ hp).mp hr

/-- Part (e): the corresponding downward perturbation, again for all large `n`. -/
theorem exercise07_e (b : ℝ) (hb : 1 < b) (y : ℝ) (hy : 0 < y) (w : ℝ)
    (hw : y < exercise06_realPower b hb w) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      y < exercise06_realPower b hb (w - 1 / (n : ℝ)) := by
  have ht : 1 < exercise06_realPower b hb w / y := by
    apply (lt_div_iff₀ hy).mpr
    simpa using hw
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - 1) / (exercise06_realPower b hb w / y - 1))
  refine ⟨max N 1, by omega, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hlarge : (b - 1) / (exercise06_realPower b hb w / y - 1) < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast (show N ≤ n by omega))
  have hr := exercise07_c b hb _ ht n hnpos hlarge
  have hm : y * exercise06_realPower b hb (1 / (n : ℝ)) <
      exercise06_realPower b hb w := by
    simpa [mul_comm] using (lt_div_iff₀ hy).mp hr
  rw [exercise06_realPower_eq_rpow, Real.rpow_sub (by linarith : 0 < b)]
  apply (lt_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < b) _)).mpr
  simpa only [exercise06_realPower_eq_rpow] using hm

/-- Rudin's set `A`, in terms of the powers actually constructed in Exercise 6. -/
def exercise07_lowerExponents (b : ℝ) (hb : 1 < b) (y : ℝ) : Set ℝ :=
  {w | exercise06_realPower b hb w < y}

/-- The set in (f) contains a negative integer exponent. -/
theorem exercise07_A_nonempty (b : ℝ) (hb : 1 < b) (y : ℝ) (hy : 0 < y) :
    (exercise07_lowerExponents b hb y).Nonempty := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt y⁻¹ hb
  refine ⟨-(n : ℝ), ?_⟩
  change exercise06_realPower b hb (-(n : ℝ)) < y
  rw [exercise06_realPower_eq_rpow, Real.rpow_neg (by linarith : 0 ≤ b), Real.rpow_natCast]
  exact (inv_lt_comm₀ (pow_pos (by linarith : 0 < b) n) hy).mpr hn

/-- The set in (f) is bounded above by an integer exponent. -/
theorem exercise07_A_bddAbove (b : ℝ) (hb : 1 < b) (y : ℝ) :
    BddAbove (exercise07_lowerExponents b hb y) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt y hb
  refine ⟨(n : ℝ), ?_⟩
  intro w hw
  have h : exercise06_realPower b hb w < exercise06_realPower b hb (n : ℝ) := by
    calc
      exercise06_realPower b hb w < y := hw
      _ < b ^ n := hn
      _ = exercise06_realPower b hb (n : ℝ) := by
        simp only [exercise06_realPower_eq_rpow, Real.rpow_natCast]
  exact ((exercise07_power_strictMono b hb).lt_iff_lt.mp h).le

/-- Part (f): the finite supremum of `A` solves the equation, by (d) and (e). -/
theorem exercise07_f (b : ℝ) (hb : 1 < b) (y : ℝ) (hy : 0 < y) :
    exercise06_realPower b hb (sSup (exercise07_lowerExponents b hb y)) = y := by
  let x := sSup (exercise07_lowerExponents b hb y)
  have hne := exercise07_A_nonempty b hb y hy
  have hbd := exercise07_A_bddAbove b hb y
  change exercise06_realPower b hb x = y
  rcases lt_trichotomy (exercise06_realPower b hb x) y with hlt | heq | hgt
  · obtain ⟨N, hN, hstep⟩ := exercise07_d b hb y x hlt
    have hm : x + 1 / (N : ℝ) ∈ exercise07_lowerExponents b hb y := hstep N le_rfl
    have hu : x + 1 / (N : ℝ) ≤ x := le_csSup hbd hm
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have := one_div_pos.mpr hNR
    linarith
  · exact heq
  · obtain ⟨N, hN, hstep⟩ := exercise07_e b hb y hy x hgt
    have hl := hstep N le_rfl
    have hu : x ≤ x - 1 / (N : ℝ) := by
      apply csSup_le hne
      intro w hw
      have hp : exercise06_realPower b hb w <
          exercise06_realPower b hb (x - 1 / (N : ℝ)) := hw.trans hl
      exact ((exercise07_power_strictMono b hb).lt_iff_lt.mp hp).le
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have := one_div_pos.mpr hNR
    linarith

/-- Part (g): any two solutions coincide. -/
theorem exercise07_g (b : ℝ) (hb : 1 < b) (y x z : ℝ)
    (hx : exercise06_realPower b hb x = y) (hz : exercise06_realPower b hb z = y) :
    x = z :=
  (exercise07_power_strictMono b hb).injective (hx.trans hz.symm)

/-- The unique solution is obtained by the specified supremum construction. -/
theorem exercise07 (b : ℝ) (hb : 1 < b) (y : ℝ) (hy : 0 < y) :
    ∃! x : ℝ, exercise06_realPower b hb x = y := by
  refine ⟨sSup (exercise07_lowerExponents b hb y), exercise07_f b hb y hy, ?_⟩
  intro z hz
  exact exercise07_g b hb y z _ hz (exercise07_f b hb y hy)

end Rudin.Chapter01
