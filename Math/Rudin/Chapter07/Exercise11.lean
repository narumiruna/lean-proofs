module

public import Mathlib

/-! # Chapter 7, Exercise 11
Uniform Dirichlet test. The three source items are hypotheses. The target
can be any complete real normed space, in particular `ℂ`. Convergence means
convergence of ordered partial sums, not unconditional summability.
Source: book page 167, PDF page 176.
-/

@[expose] public section

open Filter Set
open scoped Topology BigOperators

namespace Rudin.Chapter07

/-- Abel's estimate, with the original partial sums bounded by `B`. -/
theorem exercise11_tail_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℕ → F} {g : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ N, ‖∑ i ∈ Finset.range N, f i‖ ≤ B)
    (hg : Antitone g) (hg0 : ∀ n, 0 ≤ g n) {m n : ℕ} (hmn : m < n) :
    ‖∑ i ∈ Finset.Ico m n, g i • f i‖ ≤ 2 * B * g m := by
  have hm : m ≤ n - 1 := by omega
  rw [Finset.sum_Ico_by_parts g f hmn]
  calc
    _ ≤ ‖g (n - 1) • ∑ i ∈ Finset.range n, f i‖ +
        ‖g m • ∑ i ∈ Finset.range m, f i‖ +
        ∑ i ∈ Finset.Ico m (n - 1), ‖(g (i + 1) - g i) •
          ∑ j ∈ Finset.range (i + 1), f j‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
    _ ≤ g (n - 1) * B + g m * B +
        ∑ i ∈ Finset.Ico m (n - 1), (g i - g (i + 1)) * B := by
      apply add_le_add
      · apply add_le_add <;> rw [norm_smul, Real.norm_of_nonneg (hg0 _)]
        · exact mul_le_mul_of_nonneg_left (hf n) (hg0 _)
        · exact mul_le_mul_of_nonneg_left (hf m) (hg0 _)
      · apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hg (Nat.le_succ i))),
          neg_sub]
        exact mul_le_mul_of_nonneg_left (hf _) (sub_nonneg.mpr (hg (Nat.le_succ i)))
    _ = 2 * B * g m := by
      rw [← Finset.sum_mul]
      have ht : (∑ i ∈ Finset.Ico m (n - 1), (g i - g (i + 1))) = g m - g (n - 1) := by
        simpa only [Finset.sum_sub_distrib, neg_sub] using
          congrArg Neg.neg (Finset.sum_Ico_sub g hm)
      rw [ht]
      ring

/-- Uniform Dirichlet test with an explicit nonnegative bound. The first term
is indexed by zero; this is just a relabeling of the positive source indices. -/
theorem exercise11_uniform_dirichlet_bound {X F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {E : Set X}
    {f : ℕ → X → F} {g : ℕ → X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ N x, x ∈ E → ‖∑ i ∈ Finset.range N, f i x‖ ≤ B)
    (hu : TendstoUniformlyOn g (fun _ => 0) atTop E)
    (hg : ∀ x ∈ E, Antitone (fun n => g n x)) :
    ∃ s : X → F, TendstoUniformlyOn
      (fun N x => ∑ i ∈ Finset.range N, g i x • f i x) s atTop E := by
  have hnonneg (x : X) (hx : x ∈ E) (n : ℕ) : 0 ≤ g n x :=
    (hg x hx).le_of_tendsto (hu.tendsto_at hx) n
  have hpoint (x : X) (hx : x ∈ E) :
      ∃ s : F, Tendsto (fun N => ∑ i ∈ Finset.range N, g i x • f i x) atTop (𝓝 s) :=
    cauchySeq_tendsto_of_complete
      ((hg x hx).cauchySeq_series_mul_of_tendsto_zero_of_bounded
        (hu.tendsto_at hx) (fun N => hf N x hx))
  classical
  let s : X → F := fun x => if hx : x ∈ E then (hpoint x hx).choose else 0
  refine ⟨s, UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto ?_ ?_⟩
  · rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hden : 0 < 2 * (B + 1) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((Metric.tendstoUniformlyOn_iff.mp hu) (ε / (2 * (B + 1))) (by positivity))
    have htail (m n : ℕ) (hm : N ≤ m) (hmn : m < n) (x : X) (hx : x ∈ E) :
        ‖∑ i ∈ Finset.Ico m n, g i x • f i x‖ < ε := by
      have hb := exercise11_tail_bound hB (fun k => hf k x hx) (hg x hx)
        (hnonneg x hx) hmn
      have hsmall := hN m hm x hx
      rw [dist_zero_left, Real.norm_of_nonneg (hnonneg x hx m)] at hsmall
      have hmul := (lt_div_iff₀ hden).mp hsmall
      have hn := hnonneg x hx m
      exact hb.trans_lt (by nlinarith)
    refine ⟨N, ?_⟩
    intro m hm n hn x hx
    rcases lt_trichotomy m n with h | rfl | h
    · rw [dist_comm, dist_eq_norm, ← Finset.sum_Ico_eq_sub _ h.le]
      exact htail m n hm h x hx
    · simpa using hε
    · rw [dist_eq_norm, ← Finset.sum_Ico_eq_sub _ h.le]
      exact htail n m hn h x hx
  · intro x hx
    simpa only [s, dite_eq_left hx] using (hpoint x hx).choose_spec

/-- The source form: bounded partial sums, uniform convergence of the real
multipliers to zero, and pointwise decrease imply uniform ordered convergence.
No convergence or summability of `∑ fₙ` is assumed. -/
theorem exercise11_uniform_dirichlet {X F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {E : Set X}
    {f : ℕ → X → F} {g : ℕ → X → ℝ}
    (hf : ∃ B : ℝ, ∀ N x, x ∈ E → ‖∑ i ∈ Finset.range N, f i x‖ ≤ B)
    (hu : TendstoUniformlyOn g (fun _ => 0) atTop E)
    (hg : ∀ x ∈ E, Antitone (fun n => g n x)) :
    ∃ s : X → F, TendstoUniformlyOn
      (fun N x => ∑ i ∈ Finset.range N, g i x • f i x) s atTop E := by
  obtain ⟨B, hB⟩ := hf
  exact exercise11_uniform_dirichlet_bound (le_max_right B 0)
    (fun N x hx => (hB N x hx).trans (le_max_left B 0)) hu hg

end Rudin.Chapter07
