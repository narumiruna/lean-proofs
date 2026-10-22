module

public import Math.Rudin.Chapter04.Exercise20

@[expose] public section

namespace Rudin.Chapter04

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- The quotient prescribed in Exercise 22, with the real infima of Exercise 20. -/
noncomputable def exercise22_f (A B : Set X) (p : X) : ℝ :=
  exercise20_rho A p / (exercise20_rho A p + exercise20_rho B p)

theorem exercise22_rho_nonneg {A : Set X} (hAn : A.Nonempty) (p : X) :
    0 ≤ exercise20_rho A p := by
  rw [exercise20_rho_eq_infDist hAn]
  exact infDist_nonneg

theorem exercise22_rho_continuous {A : Set X} (hAn : A.Nonempty) :
    Continuous (exercise20_rho A) :=
  (exercise20_b_uniform_continuity hAn).continuous

theorem exercise22_rho_zero_iff {A : Set X} (hA : IsClosed A)
    (hAn : A.Nonempty) (p : X) : exercise20_rho A p = 0 ↔ p ∈ A := by
  rw [exercise20_a hAn, hA.closure_eq]

/-- The source denominator is strictly positive, so no totalized zero division is used. -/
theorem exercise22_denominator_positive {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) (p : X) :
    0 < exercise20_rho A p + exercise20_rho B p := by
  have ha := exercise22_rho_nonneg hAn p
  have hb := exercise22_rho_nonneg hBn p
  by_contra! hn
  have hza : exercise20_rho A p = 0 := by linarith
  have hzb : exercise20_rho B p = 0 := by linarith
  exact Set.disjoint_left.mp hd ((exercise22_rho_zero_iff hA hAn p).mp hza)
    ((exercise22_rho_zero_iff hB hBn p).mp hzb)

theorem exercise22_continuous {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) : Continuous (exercise22_f A B) := by
  exact (exercise22_rho_continuous hAn).div
    ((exercise22_rho_continuous hAn).add (exercise22_rho_continuous hBn))
    (fun p => (exercise22_denominator_positive hA hB hAn hBn hd p).ne')

theorem exercise22_range {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) (p : X) : exercise22_f A B p ∈ Icc (0 : ℝ) 1 := by
  have hp := exercise22_denominator_positive hA hB hAn hBn hd p
  have ha := exercise22_rho_nonneg hAn p
  have hb := exercise22_rho_nonneg hBn p
  change 0 ≤ exercise20_rho A p / _ ∧ exercise20_rho A p / _ ≤ 1
  exact ⟨div_nonneg ha hp.le, (div_le_one hp).mpr (by linarith)⟩

theorem exercise22_zero_fiber {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) (p : X) : exercise22_f A B p = 0 ↔ p ∈ A := by
  have hp := exercise22_denominator_positive hA hB hAn hBn hd p
  simp only [exercise22_f, div_eq_zero_iff, hp.ne', or_false]
  exact exercise22_rho_zero_iff hA hAn p

theorem exercise22_one_fiber {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) (p : X) : exercise22_f A B p = 1 ↔ p ∈ B := by
  have hp := exercise22_denominator_positive hA hB hAn hBn hd p
  change exercise20_rho A p / (exercise20_rho A p + exercise20_rho B p) = 1 ↔ _
  rw [div_eq_one_iff_eq hp.ne']
  have heq : exercise20_rho A p = exercise20_rho A p + exercise20_rho B p ↔
      exercise20_rho B p = 0 := by constructor <;> intro h <;> linarith
  rw [heq]
  exact exercise22_rho_zero_iff hB hBn p

/-- Every closed set, including the empty set and the entire space, is a zero set. -/
theorem exercise22_all_closed_zero_sets {C : Set X} (hC : IsClosed C) :
    ∃ h : X → ℝ, Continuous h ∧ h ⁻¹' {0} = C := by
  rcases C.eq_empty_or_nonempty with rfl | hCn
  · exact ⟨fun _ => 1, continuous_const, by ext x; simp⟩
  · refine ⟨exercise20_rho C, exercise22_rho_continuous hCn, ?_⟩
    ext x
    exact exercise22_rho_zero_iff hC hCn x

/-- The first source neighborhood uses the half-open interval [0, 1/2). -/
noncomputable def exercise22_V (A B : Set X) : Set X :=
  exercise22_f A B ⁻¹' Ico 0 (1 / 2 : ℝ)

/-- The second source neighborhood uses the half-open interval (1/2, 1]. -/
noncomputable def exercise22_W (A B : Set X) : Set X :=
  exercise22_f A B ⁻¹' Ioc (1 / 2 : ℝ) 1

/-- The intervals need not be open in ℝ: the range restriction makes the preimages open. -/
theorem exercise22_open_neighborhoods {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) : IsOpen (exercise22_V A B) ∧ IsOpen (exercise22_W A B) := by
  have hV : exercise22_V A B = exercise22_f A B ⁻¹' Iio (1 / 2 : ℝ) := by
    ext p
    exact and_iff_right (exercise22_range hA hB hAn hBn hd p).1
  have hW : exercise22_W A B = exercise22_f A B ⁻¹' Ioi (1 / 2 : ℝ) := by
    ext p
    exact and_iff_left (exercise22_range hA hB hAn hBn hd p).2
  rw [hV, hW]
  exact ⟨isOpen_Iio.preimage (exercise22_continuous hA hB hAn hBn hd),
    isOpen_Ioi.preimage (exercise22_continuous hA hB hAn hBn hd)⟩

theorem exercise22_disjoint_neighborhoods {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) :
    exercise22_V A B ∩ exercise22_W A B = ∅ ∧
      A ⊆ exercise22_V A B ∧ B ⊆ exercise22_W A B := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, hq⟩
    exact hp.2.not_gt hq.1
  · intro p hp
    change 0 ≤ exercise22_f A B p ∧ exercise22_f A B p < 1 / 2
    rw [(exercise22_zero_fiber hA hB hAn hBn hd p).mpr hp]
    norm_num
  · intro p hp
    change 1 / 2 < exercise22_f A B p ∧ exercise22_f A B p ≤ 1
    rw [(exercise22_one_fiber hA hB hAn hBn hd p).mpr hp]
    norm_num

/-- Normality also covers empty closed sets (and an empty ambient space). -/
theorem exercise22_normality {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hd : Disjoint A B) :
    ∃ V W : Set X, IsOpen V ∧ IsOpen W ∧ Disjoint V W ∧ A ⊆ V ∧ B ⊆ W := by
  rcases A.eq_empty_or_nonempty with rfl | hAn
  · exact ⟨∅, univ, isOpen_empty, isOpen_univ, by simp,
      empty_subset _, subset_univ _⟩
  rcases B.eq_empty_or_nonempty with rfl | hBn
  · exact ⟨univ, ∅, isOpen_univ, isOpen_empty, by simp,
      subset_univ _, empty_subset _⟩
  obtain ⟨hV, hW⟩ := exercise22_open_neighborhoods hA hB hAn hBn hd
  obtain ⟨hdisj, hAV, hBW⟩ := exercise22_disjoint_neighborhoods hA hB hAn hBn hd
  exact ⟨exercise22_V A B, exercise22_W A B, hV, hW,
    Set.disjoint_iff_inter_eq_empty.mpr hdisj, hAV, hBW⟩

end Rudin.Chapter04
