module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter05

/-- Uniform differentiability on a closed interval. Derivatives are taken
within the interval, so the endpoint assumptions are one-sided. -/
theorem exercise08_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : ℝ → E} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x)
    (hc : ContinuousOn d (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ t ∈ Icc a b,
      0 < |t - x| → |t - x| < δ →
      ‖(t - x)⁻¹ • (f t - f x) - d x‖ < ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx t ht hne hclose
  let s := Icc a b ∩ Metric.ball x δ
  have hs : Convex ℝ s := (convex_Icc a b).inter (convex_ball x δ)
  have hxs : x ∈ s := ⟨hx, Metric.mem_ball_self hδ⟩
  have hts : t ∈ s := ⟨ht, by simpa [Real.dist_eq] using hclose⟩
  have hb : ∀ y ∈ s, ‖d y - d x‖ ≤ ε / 2 := by
    intro y hy
    have h := hu y hy.1 x hx hy.2
    exact (show ‖d y - d x‖ < ε / 2 by simpa [dist_eq_norm] using h).le
  have hd' : ∀ y ∈ s,
      HasDerivWithinAt (fun z => f z - z • d x) (d y - d x) s y := by
    intro y hy
    simpa only [id_eq, one_smul, Pi.sub_def] using ((hd y hy.1).mono inter_subset_left).sub
      ((hasDerivAt_id y).smul_const (d x)).hasDerivWithinAt
  have hb' := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hd' hb hxs hts
  have hn : t - x ≠ 0 := (abs_pos.mp hne)
  have hn' : 0 < ‖t - x‖ := norm_pos_iff.mpr hn
  have he : f t - t • d x - (f x - x • d x) =
      f t - f x - (t - x) • d x := by
    rw [sub_smul]
    abel
  rw [he] at hb'
  have he' : (t - x)⁻¹ • (f t - f x) - d x =
      (t - x)⁻¹ • (f t - f x - (t - x) • d x) := by
    symm
    rw [smul_sub, inv_smul_smul₀ hn]
  rw [he', norm_smul, norm_inv, ← div_eq_inv_mul]
  exact lt_of_le_of_lt ((div_le_iff₀ hn').mpr hb') (by linarith)

/-- The real-valued statement, in the printed quotient notation. -/
theorem exercise08_uniform_differentiability {f d : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x)
    (hc : ContinuousOn d (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ t ∈ Icc a b,
      0 < |t - x| → |t - x| < δ → |(f t - f x) / (t - x) - d x| < ε := by
  simpa [Real.norm_eq_abs, smul_eq_mul, div_eq_inv_mul] using exercise08_uniform hd hc hε

/-- The answer to the vector question is affirmative, in Euclidean norm. -/
theorem exercise08_vector_version {k : ℕ} {f d : ℝ → EuclideanSpace ℝ (Fin k)} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x)
    (hc : ContinuousOn d (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ t ∈ Icc a b,
      0 < |t - x| → |t - x| < δ →
      ‖(t - x)⁻¹ • (f t - f x) - d x‖ < ε :=
  exercise08_uniform hd hc hε

end Rudin.Chapter05
