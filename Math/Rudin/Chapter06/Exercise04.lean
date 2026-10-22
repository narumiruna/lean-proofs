module

public import Math.Rudin.Support.StieltjesIntegralLaws
public import Mathlib.NumberTheory.Real.Irrational

/-!
# R06E04: the rational indicator

Source: Rudin, Third Edition, Exercise 6.4, book page 138 (PDF page 147).
On every interval `a < b`, the literal lower integral is zero and the
literal upper integral is `b - a`. Closed cells and repeated partition nodes
are retained. These are Riemann integrals with integrator `id`, not Lebesgue
integrals.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesEquivalence
open Rudin.Support.StieltjesIntegralLaws

/-- One at rational points and zero at irrational points. -/
noncomputable def rationalIndicator (x : ℝ) : ℝ := by
  classical
  exact if x ∈ Set.range ((↑) : ℚ → ℝ) then 1 else 0

@[simp] theorem rationalIndicator_rat (q : ℚ) : rationalIndicator q = 1 := by
  simp [rationalIndicator]

theorem rationalIndicator_irrational {x : ℝ} (hx : Irrational x) :
    rationalIndicator x = 0 := by
  exact ite_eq_right hx

/-- The indicator is bounded on the whole real line. -/
theorem rationalIndicator_bounds (x : ℝ) :
    0 ≤ rationalIndicator x ∧ rationalIndicator x ≤ 1 := by
  unfold rationalIndicator
  split_ifs <;> norm_num

private theorem rationalIndicator_image {s t : ℝ} (hst : s < t) :
    rationalIndicator '' Icc s t = {0, 1} := by
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    unfold rationalIndicator
    split_ifs <;> simp
  · intro hy
    rcases (show y = 0 ∨ y = 1 by simpa using hy) with rfl | rfl
    · obtain ⟨x, hx, hs, ht⟩ := exists_irrational_btwn hst
      exact ⟨x, ⟨hs.le, ht.le⟩, rationalIndicator_irrational hx⟩
    · obtain ⟨q, hs, ht⟩ := exists_rat_btwn hst
      exact ⟨q, ⟨hs.le, ht.le⟩, rationalIndicator_rat q⟩

/-- Every lower sum is zero, also when some cells have zero length. -/
theorem rationalIndicator_lowerSum {a b : ℝ} (p : Partition a b) :
    lowerSum p rationalIndicator id = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hle := (left_isTag p i (Finset.mem_range.mp hi)).2
  rcases lt_or_eq_of_le hle with hlt | heq
  · simp [rationalIndicator_image hlt]
  · simp [heq]

/-- Every upper sum equals the interval length. -/
theorem rationalIndicator_upperSum {a b : ℝ} (p : Partition a b) :
    upperSum p rationalIndicator id = b - a := by
  have heq : upperSum p rationalIndicator id = upperSum p (fun _ ↦ 1) id := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle := (left_isTag p i hi').2
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [rationalIndicator_image hlt]
      have hc : (fun _ : ℝ ↦ (1 : ℝ)) '' Icc (p.x i) (p.x (i + 1)) = {1} := by
        ext y
        simp only [mem_image, mem_singleton_iff]
        constructor
        · rintro ⟨_, _, rfl⟩; rfl
        · rintro rfl; exact ⟨p.x i, left_isTag p i hi', rfl⟩
      rw [hc]
      simp
    · simp [heq]
  rw [heq, upperSum_const]
  simp

/-- The two raw Darboux extrema differ by exactly `b - a`. -/
theorem exercise04_darboux_extrema {a b : ℝ} (hab : a ≤ b) :
    sSup (Set.range fun p : Partition a b ↦ lowerSum p rationalIndicator id) = 0 ∧
    sInf (Set.range fun p : Partition a b ↦ upperSum p rationalIndicator id) = b - a := by
  let : Nonempty (Partition a b) := ⟨single hab⟩
  simp only [rationalIndicator_lowerSum, rationalIndicator_upperSum,
    Set.range_const, csSup_singleton, csInf_singleton, and_self]

/-- R06E04: no value is a Riemann integral of the rational indicator if `a < b`. -/
theorem exercise04 {a b : ℝ} (hab : a < b) :
    ¬ ∃ v : ℝ, HasDarbouxRSIntegral rationalIndicator id a b v := by
  rintro ⟨v, hv⟩
  obtain ⟨hl, hu⟩ := exercise04_darboux_extrema hab.le
  have h₀ : (0 : ℝ) = v := hl.symm.trans hv.2.2.1
  have h₁ : b - a = v := hu.symm.trans hv.2.2.2
  linarith

/-- The same nonintegrability for the proved equivalent raw tagged predicate. -/
theorem exercise04_tagged {a b : ℝ} (hab : a < b) :
    ¬ ∃ v : ℝ, HasRSIntegral rationalIndicator id a b v := by
  rintro ⟨v, hv⟩
  exact exercise04 hab ⟨v, hasDarbouxRSIntegral_of_hasRSIntegral hab.le hv⟩

/-- Source formulation for any function with the stated rational/irrational values. -/
theorem exercise04_source {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hr : ∀ q : ℚ, (q : ℝ) ∈ Icc a b → f q = 1)
    (hi : ∀ x ∈ Icc a b, Irrational x → f x = 0) :
    ¬ ∃ v : ℝ, HasDarbouxRSIntegral f id a b v := by
  rintro ⟨v, hv⟩
  apply exercise04 hab
  refine ⟨v, hasDarbouxRSIntegral_congr hab.le hv ?_⟩
  intro x hx
  by_cases hq : x ∈ Set.range ((↑) : ℚ → ℝ)
  · obtain ⟨q, rfl⟩ := hq
    rw [hr q hx, rationalIndicator_rat]
  · rw [hi x hx hq, rationalIndicator_irrational hq]

end Rudin.Chapter06
