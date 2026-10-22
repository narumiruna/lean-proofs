module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

/-!
# R01E06: powers from positive roots and suprema

Source: Rudin, Third Edition, book page 22 (PDF page 31).
The source uses `t ≤ x` in the definition of `B(x)`.
Positive roots are chosen from their defining integer-power equation. Rational
powers use these roots; real powers are the actual suprema of lower rational
powers. The comparison with `Real.rpow` is proved, not used as a definition.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- Existence and uniqueness of the positive root, including integer indices. -/
theorem exercise06_root_exists (a : ℝ) (n : ℤ) (ha : 0 < a) (hn : 0 < n) :
    ∃! u : ℝ, 0 < u ∧ u ^ n = a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨a ^ (1 / (n : ℝ)), ⟨Real.rpow_pos_of_pos ha _, ?_⟩, ?_⟩
  · rw [← Real.rpow_intCast, ← Real.rpow_mul ha.le]
    simp [ne_of_gt hnR]
  · intro u hu
    have h := congrArg (fun v : ℝ => v ^ (1 / (n : ℝ))) hu.2
    rw [← Real.rpow_intCast, ← Real.rpow_mul hu.1.le] at h
    simpa [ne_of_gt hnR] using h

/-- The positive root is selected by its equation, not by a power formula. -/
noncomputable def exercise06_positiveRoot (a : ℝ) (n : ℤ)
    (ha : 0 < a) (hn : 0 < n) : ℝ :=
  Classical.choose (exercise06_root_exists a n ha hn)

theorem exercise06_root_spec (a : ℝ) (n : ℤ) (ha : 0 < a) (hn : 0 < n) :
    0 < exercise06_positiveRoot a n ha hn ∧
      exercise06_positiveRoot a n ha hn ^ n = a :=
  (Classical.choose_spec (exercise06_root_exists a n ha hn)).1

theorem exercise06_root_eq_rpow (a : ℝ) (n : ℤ) (ha : 0 < a) (hn : 0 < n) :
    exercise06_positiveRoot a n ha hn = a ^ (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := congrArg (fun v : ℝ => v ^ (1 / (n : ℝ)))
    (exercise06_root_spec a n ha hn).2
  rw [← Real.rpow_intCast, ← Real.rpow_mul (exercise06_root_spec a n ha hn).1.le] at h
  simpa [ne_of_gt hnR] using h

/-- Comparison of an integer-power root with the corresponding rational exponent. -/
theorem exercise06_fraction_eq_rpow (b : ℝ) (hb : 1 < b) (m n : ℤ) (hn : 0 < n) :
    exercise06_positiveRoot (b ^ m) n (zpow_pos (by linarith) _) hn =
      b ^ ((m : ℝ) / (n : ℝ)) := by
  rw [exercise06_root_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (by linarith : 0 ≤ b)]
  congr 1
  ring

/-- Part (a): independence of the integer fraction representation. -/
theorem exercise06_a (b : ℝ) (hb : 1 < b) (m n p q : ℤ)
    (hn : 0 < n) (hq : 0 < q) (h : (m : ℚ) / n = (p : ℚ) / q) :
    exercise06_positiveRoot (b ^ m) n (zpow_pos (by linarith) _) hn =
      exercise06_positiveRoot (b ^ p) q (zpow_pos (by linarith) _) hq := by
  rw [exercise06_fraction_eq_rpow b hb, exercise06_fraction_eq_rpow b hb]
  congr 1
  exact_mod_cast h

/-- Rational powers use the positive root of the integer power of the base. -/
noncomputable def exercise06_rationalPower (b : ℝ) (hb : 1 < b) (r : ℚ) : ℝ :=
  exercise06_positiveRoot (b ^ r.num) (r.den : ℤ)
    (zpow_pos (by linarith) _) (by exact_mod_cast r.den_pos)

theorem exercise06_rationalPower_eq_rpow (b : ℝ) (hb : 1 < b) (r : ℚ) :
    exercise06_rationalPower b hb r = b ^ (r : ℝ) := by
  unfold exercise06_rationalPower
  rw [exercise06_fraction_eq_rpow b hb]
  congr 1
  simpa using (Rat.cast_def r : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ)).symm

/-- Every fraction, not only the reduced fraction, gives the defined rational power. -/
theorem exercise06_rationalPower_fraction (b : ℝ) (hb : 1 < b) (m n : ℤ)
    (hn : 0 < n) :
    exercise06_rationalPower b hb ((m : ℚ) / n) =
      exercise06_positiveRoot (b ^ m) n (zpow_pos (by linarith) _) hn := by
  rw [exercise06_rationalPower_eq_rpow, exercise06_fraction_eq_rpow b hb]
  norm_cast

/-- Part (b): the addition law for the root-defined rational powers. -/
theorem exercise06_b (b : ℝ) (hb : 1 < b) (r s : ℚ) :
    exercise06_rationalPower b hb (r + s) =
      exercise06_rationalPower b hb r * exercise06_rationalPower b hb s := by
  simp only [exercise06_rationalPower_eq_rpow, Rat.cast_add]
  exact Real.rpow_add (by linarith) _ _

/-- Rudin's set `B(x)`, with the non-strict source inequality. -/
def exercise06_lowerPowers (b : ℝ) (hb : 1 < b) (x : ℝ) : Set ℝ :=
  {v | ∃ t : ℚ, (t : ℝ) ≤ x ∧ v = exercise06_rationalPower b hb t}

theorem exercise06_lowerPowers_nonempty (b : ℝ) (hb : 1 < b) (x : ℝ) :
    (exercise06_lowerPowers b hb x).Nonempty := by
  obtain ⟨t, ht⟩ := exists_rat_lt x
  exact ⟨_, t, ht.le, rfl⟩

theorem exercise06_lowerPowers_bddAbove (b : ℝ) (hb : 1 < b) (x : ℝ) :
    BddAbove (exercise06_lowerPowers b hb x) := by
  refine ⟨b ^ x, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  rw [exercise06_rationalPower_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hb.le ht

/-- The real power is the source-defined supremum. -/
noncomputable def exercise06_realPower (b : ℝ) (hb : 1 < b) (x : ℝ) : ℝ :=
  sSup (exercise06_lowerPowers b hb x)

/-- Part (c), at rational arguments: the set has its rational power as a maximum. -/
theorem exercise06_c_supremum (b : ℝ) (hb : 1 < b) (r : ℚ) :
    exercise06_rationalPower b hb r = sSup (exercise06_lowerPowers b hb r) := by
  apply le_antisymm
  · exact le_csSup (exercise06_lowerPowers_bddAbove b hb r) ⟨r, le_rfl, rfl⟩
  · apply csSup_le (exercise06_lowerPowers_nonempty b hb r)
    rintro v ⟨t, ht, rfl⟩
    simp only [exercise06_rationalPower_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hb.le ht

/-- Identification of the source-defined supremum, using continuity and rational density. -/
theorem exercise06_realPower_eq_rpow (b : ℝ) (hb : 1 < b) (x : ℝ) :
    exercise06_realPower b hb x = b ^ x := by
  apply le_antisymm
  · apply csSup_le (exercise06_lowerPowers_nonempty b hb x)
    rintro v ⟨t, ht, rfl⟩
    rw [exercise06_rationalPower_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hb.le ht
  · apply le_of_forall_lt
    intro z hz
    obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp
      (Real.continuousAt_const_rpow (a := b) (b := x) (by linarith))
      (b ^ x - z) (sub_pos.mpr hz)
    obtain ⟨t, ht₁, ht₂⟩ := exists_rat_btwn (sub_lt_self x hδ)
    have hd : dist (t : ℝ) x < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht₂)]
      linarith
    have hp := hc hd
    rw [Real.dist_eq, abs_lt] at hp
    have hz' : z < exercise06_rationalPower b hb t := by
      rw [exercise06_rationalPower_eq_rpow]
      linarith [hp.1]
    exact hz'.trans_le (le_csSup (exercise06_lowerPowers_bddAbove b hb x)
      ⟨t, ht₂.le, rfl⟩)

/-- Part (c): the supremum definition extends the root-defined rational powers. -/
theorem exercise06_c_real_power (b : ℝ) (hb : 1 < b) (r : ℚ) :
    exercise06_realPower b hb (r : ℝ) = exercise06_rationalPower b hb r :=
  (exercise06_c_supremum b hb r).symm

/-- Part (d): the addition law for the supremum-defined real powers. -/
theorem exercise06_d (b : ℝ) (hb : 1 < b) (x y : ℝ) :
    exercise06_realPower b hb (x + y) =
      exercise06_realPower b hb x * exercise06_realPower b hb y := by
  simp only [exercise06_realPower_eq_rpow]
  exact Real.rpow_add (by linarith) _ _

end Rudin.Chapter01
