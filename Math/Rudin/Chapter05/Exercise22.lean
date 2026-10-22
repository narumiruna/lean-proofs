module

public import Mathlib

@[expose] public section
noncomputable section
open Set Filter Function
open scoped Topology NNReal
namespace Rudin.Chapter05

/-- Rolle's theorem gives uniqueness without a uniform contraction bound. -/
theorem exercise22_a {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hd : ∀ t, deriv f t ≠ 1) {x y : ℝ} (hx : f x = x) (hy : f y = y) : x = y := by
  suffices h : ∀ a b : ℝ, f a = a → f b = b → ¬ a < b by
    exact le_antisymm (le_of_not_gt (h y x hy hx)) (le_of_not_gt (h x y hx hy))
  intro a b ha hb hab
  obtain ⟨c, _, hc⟩ := exists_deriv_eq_slope f hab hf.continuous.continuousOn
    hf.differentiableOn
  rw [ha, hb, div_self (sub_ne_zero.mpr hab.ne')] at hc
  exact hd c hc

/-- The counterexample has a positive displacement at every real argument. -/
def exercise22Example (t : ℝ) : ℝ := t + 1 / (1 + Real.exp t)

theorem exercise22_b_no_fixed_point (t : ℝ) : exercise22Example t ≠ t := by
  have : 0 < 1 / (1 + Real.exp t) := by positivity
  unfold exercise22Example
  linarith

theorem exercise22_b_hasDerivAt (t : ℝ) :
    HasDerivAt exercise22Example (1 - Real.exp t / (1 + Real.exp t)^2) t := by
  have he := (hasDerivAt_id t).add
    ((hasDerivAt_const t (1 : ℝ)).div
      ((hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_exp t))
      (by change 1 + Real.exp t ≠ 0; positivity))
  convert he using 1
  · rfl
  · dsimp
    ring

theorem exercise22_b_derivative (t : ℝ) :
    0 < deriv exercise22Example t ∧ deriv exercise22Example t < 1 := by
  rw [(exercise22_b_hasDerivAt t).deriv]
  have he := Real.exp_pos t
  have hp : 0 < (1 + Real.exp t)^2 := by positivity
  have hq : 0 < Real.exp t / (1 + Real.exp t)^2 := div_pos he hp
  have hl : Real.exp t / (1 + Real.exp t)^2 < 1 :=
    (div_lt_one hp).2 (by nlinarith [sq_nonneg (Real.exp t)])
  constructor <;> linarith

/-- The derivative bound gives a contraction on the complete real line. -/
theorem exercise22_c {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {A : ℝ} (hA : A < 1) (hd : ∀ t, |deriv f t| ≤ A) :
    ∃! z : ℝ, f z = z ∧ ∀ x : ℝ,
      Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 z) := by
  have hnonneg : 0 ≤ A := (abs_nonneg (deriv f 0)).trans (hd 0)
  let K : ℝ≥0 := ⟨A, hnonneg⟩
  have hc : ContractingWith K f := ⟨hA,
    lipschitzWith_of_nnnorm_deriv_le hf (fun t => by
      change ‖deriv f t‖ ≤ A
      simpa only [Real.norm_eq_abs] using hd t)⟩
  refine ⟨hc.fixedPoint f, ⟨hc.fixedPoint_isFixedPt, hc.tendsto_iterate_fixedPoint⟩, ?_⟩
  intro y hy
  exact hc.fixedPoint_unique hy.1

/-- In particular, the contraction has exactly one fixed point. -/
theorem exercise22_c_existence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {A : ℝ} (hA : A < 1) (hd : ∀ t, |deriv f t| ≤ A) : ∃! z : ℝ, f z = z := by
  obtain ⟨z, ⟨hz, ht⟩, _⟩ := exercise22_c hf hA hd
  refine ⟨z, hz, ?_⟩
  intro y hy
  have he : ∀ n : ℕ, f^[n] y = y := fun n => (show IsFixedPt f y from hy).iterate n
  have hty : Tendsto (fun _ : ℕ => y) atTop (𝓝 z) := by
    simpa only [he] using ht y
  exact tendsto_nhds_unique tendsto_const_nhds hty

/-- The limit is the fixed point, for every initial real number. -/
theorem exercise22_c_iteration {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {A : ℝ} (hA : A < 1) (hd : ∀ t, |deriv f t| ≤ A)
    {z : ℝ} (hz : f z = z) (x : ℝ) :
    Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 z) := by
  obtain ⟨w, ⟨hw, ht⟩, _⟩ := exercise22_c hf hA hd
  obtain ⟨v, _, hv⟩ := exercise22_c_existence hf hA hd
  have he : w = z := (hv w hw).trans (hv z hz).symm
  simpa only [he] using ht x

/-- Source index 1 corresponds to index 0 here. -/
def exercise22Orbit (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ := f^[n] x

@[simp] theorem exercise22Orbit_succ (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    exercise22Orbit f x (n+1) = f (exercise22Orbit f x n) :=
  Function.iterate_succ_apply' f n x

/-- The graph vertex at step `n`. -/
def exercise22Graph (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ × ℝ :=
  (exercise22Orbit f x n, exercise22Orbit f x (n+1))

/-- The next diagonal vertex. -/
def exercise22Diagonal (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ × ℝ :=
  (exercise22Orbit f x (n+1), exercise22Orbit f x (n+1))

/-- Exact horizontal and vertical segments of the cobweb, including degenerate segments. -/
theorem exercise22_d_segments (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    segment ℝ (exercise22Graph f x n) (exercise22Diagonal f x n) =
      {p | p.1 ∈ uIcc (exercise22Orbit f x n) (exercise22Orbit f x (n+1)) ∧
        p.2 = exercise22Orbit f x (n+1)} ∧
    segment ℝ (exercise22Diagonal f x n) (exercise22Graph f x (n+1)) =
      {p | p.1 = exercise22Orbit f x (n+1) ∧
        p.2 ∈ uIcc (exercise22Orbit f x (n+1)) (exercise22Orbit f x (n+2))} := by
  constructor
  · rw [exercise22Graph, exercise22Diagonal, ← Prod.image_mk_segment_left,
      segment_eq_uIcc]
    ext ⟨p, q⟩
    simp [eq_comm]
  · rw [exercise22Diagonal, exercise22Graph, ← Prod.image_mk_segment_right,
      segment_eq_uIcc]
    ext ⟨p, q⟩
    simp [eq_comm, and_comm]

/-- The horizontal leg ends on the diagonal; the vertical leg ends on the graph. -/
theorem exercise22_d_vertices (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    (exercise22Graph f x n).2 = f (exercise22Graph f x n).1 ∧
    (exercise22Diagonal f x n).1 = (exercise22Diagonal f x n).2 ∧
    (exercise22Graph f x (n+1)).2 = f (exercise22Graph f x (n+1)).1 := by
  simp [exercise22Graph, exercise22Diagonal]

end Rudin.Chapter05
