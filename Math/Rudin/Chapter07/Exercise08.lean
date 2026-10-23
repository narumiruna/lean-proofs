module

public import Mathlib

/-! # Chapter 7, Exercise 8
The left step has value zero at its jump. Coefficients can be complex, or lie
in any complete real normed space. Source: book page 166, PDF page 175.
-/

@[expose] public section

open Filter Set
open scoped Topology BigOperators

namespace Rudin.Chapter07

noncomputable section

def exercise08Step (x : ℝ) : ℝ := if x ≤ 0 then 0 else 1

def exercise08Term {F : Type*} [Zero F] (c : ℕ → F) (p : ℕ → ℝ)
    (n : ℕ) (x : ℝ) : F := if p n < x then c n else 0

def exercise08Sum {F : Type*} [NormedAddCommGroup F] (c : ℕ → F)
    (p : ℕ → ℝ) (x : ℝ) : F := ∑' n, exercise08Term c p n x

theorem exercise08_step_zero : exercise08Step 0 = 0 := by simp [exercise08Step]

theorem exercise08_source_term {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℕ → F) (p : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    exercise08Term c p n x = exercise08Step (x - p n) • c n := by
  simp only [exercise08Term, exercise08Step, sub_nonpos]
  by_cases h : p n < x
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

/-- The absolute-convergence hypothesis is ordinary ordered convergence.
Nonnegativity proves the bridge to `Summable`. -/
theorem exercise08_absolute_bridge {F : Type*} [NormedAddCommGroup F] {c : ℕ → F}
    (hc : ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ‖c n‖) atTop (𝓝 s)) :
    Summable (fun n => ‖c n‖) := by
  obtain ⟨s, hs⟩ := hc
  exact ((hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg (c n)) s).mpr hs).summable

/-- In fact the series converges uniformly on the whole line. -/
theorem exercise08_uniform_global {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {c : ℕ → F} (p : ℕ → ℝ) (hc : Summable (fun n => ‖c n‖)) :
    TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, exercise08Term c p n x)
      (exercise08Sum c p) atTop := by
  apply tendstoUniformly_tsum_nat hc
  intro n x
  by_cases h : p n < x <;> simp [exercise08Term, h]

/-- Source hypotheses, with distinct jump points strictly between the endpoints. -/
theorem exercise08_uniform_series {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {a b : ℝ} {c : ℕ → F} {p : ℕ → ℝ}
    (_hp : Function.Injective p) (_hmem : ∀ n, p n ∈ Ioo a b)
    (hc : ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ‖c n‖) atTop (𝓝 s)) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, exercise08Term c p n x)
      (exercise08Sum c p) atTop (Icc a b) :=
  (exercise08_uniform_global p (exercise08_absolute_bridge hc)).tendstoUniformlyOn

/-- Uniform limits preserve continuity at a single point. The neighborhoods for
different approximating functions need not have a common radius. -/
theorem exercise08_continuousAt_of_uniform {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {F : ℕ → X → Y} {f : X → Y} {x : X}
    (hu : TendstoUniformly F f atTop) (hc : ∀ n, ContinuousAt (F n) x) :
    ContinuousAt f x := by
  apply continuousAt_of_locally_uniform_approx_of_continuousAt
  intro u hu'
  obtain ⟨n, hn⟩ := (hu u hu').exists
  exact ⟨univ, univ_mem, F n, hc n, fun y _ => hn y⟩

theorem exercise08_term_continuousAt {F : Type*} [NormedAddCommGroup F]
    (c : ℕ → F) (p : ℕ → ℝ) (n : ℕ) {x : ℝ} (hx : x ≠ p n) :
    ContinuousAt (exercise08Term c p n) x := by
  by_cases h : p n < x
  · apply (continuousAt_const (y := c n)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with y hy
    simp [exercise08Term, hy]
  · have h' : x < p n := lt_of_le_of_ne (le_of_not_gt h) hx
    apply (continuousAt_const (y := (0 : F))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h'] with y hy
    simp [exercise08Term, not_lt.mpr hy.le]

/-- This includes accumulation points of all jumps, and both interval endpoints.
The stronger ambient continuity statement also fixes the relative endpoint convention. -/
theorem exercise08_continuity_off_jumps {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {a b : ℝ} {c : ℕ → F} {p : ℕ → ℝ}
    (_hp : Function.Injective p) (_hmem : ∀ n, p n ∈ Ioo a b)
    (hc : ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ‖c n‖) atTop (𝓝 s))
    {x : ℝ} (_hx : x ∈ Icc a b) (hoff : ∀ n, x ≠ p n) :
    ContinuousAt (exercise08Sum c p) x := by
  apply exercise08_continuousAt_of_uniform
    (exercise08_uniform_global p (exercise08_absolute_bridge hc))
  intro N
  have hc : ∀ n, ContinuousAt (exercise08Term c p n) x :=
    fun n => exercise08_term_continuousAt c p n (hoff n)
  fun_prop

end

end Rudin.Chapter07
