module

public import Math.Rudin.Chapter07.Exercise01

/-!
# R07E02: uniform limits of sums and bounded products

Source: Rudin, Third Edition, book page 165 (PDF 174).
No uniform bound is assumed initially; it follows from Exercise 1.
-/

@[expose] public section

namespace Rudin.Chapter07

open Set Filter
open scoped Topology

theorem exercise02_sums {X E : Type*} [NormedAddCommGroup E]
    {F G : ℕ → X → E} {f g : X → E} {s : Set X}
    (hF : TendstoUniformlyOn F f atTop s) (hG : TendstoUniformlyOn G g atTop s) :
    TendstoUniformlyOn (fun n x => F n x + G n x) (fun x => f x + g x) atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hG (ε / 2) (by positivity)] with n hnF hnG
  intro x hx
  have hf : ‖f x - F n x‖ < ε / 2 := by simpa only [dist_eq_norm] using hnF x hx
  have hg : ‖g x - G n x‖ < ε / 2 := by simpa only [dist_eq_norm] using hnG x hx
  have he : f x + g x - (F n x + G n x) = (f x - F n x) + (g x - G n x) := by abel
  rw [dist_eq_norm, he]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Individual boundedness suffices for uniform product convergence.
The normed-ring formulation includes both real and complex functions. -/
theorem exercise02_products {X K : Type*} [NormedRing K]
    {F G : ℕ → X → K} {f g : X → K} {s : Set X}
    (hF : TendstoUniformlyOn F f atTop s) (hG : TendstoUniformlyOn G g atTop s)
    (hFb : ∀ n, ∃ M : ℝ, ∀ x ∈ s, ‖F n x‖ ≤ M)
    (hGb : ∀ n, ∃ M : ℝ, ∀ x ∈ s, ‖G n x‖ ≤ M) :
    TendstoUniformlyOn (fun n x => F n x * G n x) (fun x => f x * g x) atTop s := by
  obtain ⟨M, hM⟩ := exercise01_uniform_bound hF hFb
  obtain ⟨N, hN⟩ := exercise01_uniform_bound hG hGb
  have hMf : ∀ n x, x ∈ s → ‖F n x‖ ≤ |M| :=
    fun n x hx => (hM n x hx).trans (le_abs_self M)
  have hNg : ∀ x ∈ s, ‖g x‖ ≤ |N| := by
    intro x hx
    exact le_of_tendsto (hG.tendsto_at hx).norm
      (Eventually.of_forall fun n => (hN n x hx).trans (le_abs_self N))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (|M| + |N| + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hscale : δ * (|M| + |N| + 1) = ε := div_mul_cancel₀ _ (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hG δ hδ] with n hnF hnG
  intro x hx
  have hf : ‖f x - F n x‖ < δ := by simpa only [dist_eq_norm] using hnF x hx
  have hg : ‖g x - G n x‖ < δ := by simpa only [dist_eq_norm] using hnG x hx
  have he : f x * g x - F n x * G n x =
      (f x - F n x) * g x + F n x * (g x - G n x) := by noncomm_ring
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖(f x - F n x) * g x‖ + ‖F n x * (g x - G n x)‖ := norm_add_le _ _
    _ ≤ ‖f x - F n x‖ * ‖g x‖ + ‖F n x‖ * ‖g x - G n x‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ δ * |N| + |M| * δ := add_le_add
      (mul_le_mul hf.le (hNg x hx) (norm_nonneg _) hδ.le)
      (mul_le_mul (hMf n x hx) hg.le (norm_nonneg _) (abs_nonneg M))
    _ < ε := by nlinarith

end Rudin.Chapter07
