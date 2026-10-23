module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Tactic

/-! # The second derivative test and the singular obstruction

A nonzero Hessian need not determine the type of a critical point. The
quadratic expansion supports definite tests and one-sided exclusions, but
singular semidefinite cases require more information.
-/

@[expose] public section
noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff
namespace Rudin.Chapter09

section QuadraticBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positivity on all nonzero vectors gives a uniform quadratic lower bound. -/
theorem exercise31_quadratic_lower_bound [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x ≠ 0, 0 < B x x) :
    ∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ B x x := by
  have hcont : Continuous (fun x ↦ B x x) := by fun_prop
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hcont.continuousOn (fun x hx ↦ hB x (by
      have hn : ‖x‖ = 1 := by simpa using hx
      intro he; simp [he] at hn))
  refine ⟨c, hc, fun x ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, hn]
  have hb := hbound (‖x‖⁻¹ • x) hs
  simp only [map_smul, smul_apply, smul_eq_mul] at hb
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
  convert hm using 1
  field_simp

/-- Explicit expansion predicate; the source C3 hypothesis will supply this result. -/
def exercise31QuadraticExpansion (f : E → ℝ) (a : E) (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  (fun h ↦ f (a + h) - f a - B h h / 2) =o[𝓝 0] (fun h ↦ ‖h‖ ^ 2)

/-- Integrate the first-derivative error on a ball to obtain the quadratic error.
All first derivatives and the second derivative are genuine jet witnesses. -/
theorem exercise31_peano_of_jet {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {a : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ᶠ x in 𝓝 a, HasFDerivAt f (f' x) x)
    (hd : HasFDerivAt f' B a) (hz : f' a = 0) :
    exercise31QuadraticExpansion f a B := by
  have hsym := second_derivative_symmetric_of_eventually_of_real hf hd
  have hq (x : E) : HasFDerivAt (fun y ↦ B (y - a) (y - a) / 2) (B (x - a)) x := by
    have hi := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const a
    have hb := (B.hasFDerivAt.comp x hi).clm_apply hi
    convert hb.const_mul (1 / 2 : ℝ) using 1
    · ext y
      simp only [Function.comp_apply, id_eq]
      ring
    · ext v
      simp only [smul_apply, add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.flip_apply, smul_eq_mul, Function.comp_apply, id_eq]
      rw [hsym v (x - a)]
      ring
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hf
  have he : (fun x ↦ f' x - B (x - a)) =o[𝓝 a] (fun x ↦ ‖x - a‖ ^ 1) := by
    simpa only [hz, sub_zero, pow_one] using (hasFDerivAt_iff_isLittleO.mp hd).norm_right
  have hi := (convex_ball a r).isLittleO_pow_succ (Metric.mem_ball_self hr)
    (f := fun x ↦ f x - f a - B (x - a) (x - a) / 2)
    (f' := fun x ↦ f' x - B (x - a))
    (fun x hx ↦ ((hball hx).sub_const (f a) |>.sub (hq x)).hasFDerivWithinAt)
    (he.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds a hr)] at hi
  have ht : Tendsto (fun h : E ↦ a + h) (𝓝 0) (𝓝 a) := by
    simpa only [add_zero] using (continuous_const_add a).tendsto (0 : E)
  have hi' : (fun x ↦ f x - f a - B (x - a) (x - a) / 2) =o[𝓝 a]
      (fun x ↦ ‖x - a‖ ^ 2) := by
    simpa only [sub_self, map_zero, zero_apply, zero_div, sub_zero]
      using hi
  unfold exercise31QuadraticExpansion
  convert hi'.comp_tendsto ht using 1 <;> ext h <;>
    simp only [Function.comp_apply, add_sub_cancel_left]

/-- The source's C3 hypothesis supplies the actual quadratic expansion. -/
theorem exercise31_quadratic_expansion {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ 3 f a) (hz : fderiv ℝ f a = 0) :
    exercise31QuadraticExpansion f a (fderiv ℝ (fderiv ℝ f) a) := by
  apply exercise31_peano_of_jet (f' := fderiv ℝ f) ?_ ?_ hz
  · filter_upwards [hf.eventually (by norm_num)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasFDerivAt
  · exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt

/-- A strict local minimum is stated with the full punctured neighborhood. -/
def exercise31StrictMin (f : E → ℝ) (a : E) : Prop :=
  ∃ δ > 0, ∀ h : E, ‖h‖ < δ → h ≠ 0 → f a < f (a + h)

def exercise31StrictMax (f : E → ℝ) (a : E) : Prop :=
  ∃ δ > 0, ∀ h : E, ‖h‖ < δ → h ≠ 0 → f (a + h) < f a

theorem exercise31_strict_min_of_expansion [FiniteDimensional ℝ E] {f : E → ℝ} {a : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : exercise31QuadraticExpansion f a B)
    (hB : ∀ x ≠ 0, 0 < B x x) : exercise31StrictMin f a := by
  obtain ⟨c, hc, hbound⟩ := exercise31_quadratic_lower_bound B hB
  have he := hf.bound (show 0 < c / 4 by positivity)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, fun h hh hn ↦ ?_⟩
  have hb := hδbound (by simpa using hh)
  have hs : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hl := hbound h
  have ha : -(c / 4 * ‖h‖ ^ 2) ≤ f (a + h) - f a - B h h / 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using (abs_le.mp hb).1
  nlinarith

theorem exercise31_strict_max_of_expansion [FiniteDimensional ℝ E] {f : E → ℝ} {a : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : exercise31QuadraticExpansion f a B)
    (hB : ∀ x ≠ 0, B x x < 0) : exercise31StrictMax f a := by
  have he : exercise31QuadraticExpansion (fun x ↦ -f x) a (-B) := by
    unfold exercise31QuadraticExpansion at hf ⊢
    convert hf.neg_left using 1
    ext h
    simp
    ring
  obtain ⟨δ, hδ, hb⟩ := exercise31_strict_min_of_expansion he
    (fun x hx ↦ by simpa using hB x hx)
  exact ⟨δ, hδ, fun h hh hn ↦ by simpa using hb h hh hn⟩

/-- A positive quadratic direction excludes a local maximum. -/
theorem exercise31_not_max_of_positive_direction {f : E → ℝ} {a : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : exercise31QuadraticExpansion f a B)
    {v : E} (hv : 0 < B v v) : ¬ IsLocalMax f a := by
  intro hm
  have hn : ‖v‖ ≠ 0 := by
    intro he
    have hz : v = 0 := norm_eq_zero.mp he
    simp [hz] at hv
  let c := B v v / (4 * ‖v‖ ^ 2)
  have hc : 0 < c := div_pos hv (by positivity)
  have hcLine : Continuous (fun t : ℝ ↦ t • v) := by fun_prop
  have ht : Tendsto (fun t : ℝ ↦ t • v) (𝓝 0) (𝓝 (0 : E)) := by
    simpa using hcLine.tendsto (0 : ℝ)
  have ht' : Tendsto (fun t : ℝ ↦ a + t • v) (𝓝 0) (𝓝 a) := by
    simpa using (hcLine.const_add a).tendsto (0 : ℝ)
  have he := (ht.eventually (hf.bound hc)).and (ht'.eventually hm)
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp he
  let t := r / 2
  have htpos : 0 < t := by dsimp [t]; positivity
  have htnear : dist t 0 < r := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos htpos]
    dsimp [t]; linarith
  obtain ⟨he, hm⟩ := hbound htnear
  have hq : B (t • v) (t • v) = t ^ 2 * B v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  have hnrm : c * ‖‖t • v‖ ^ 2‖ = t ^ 2 * B v v / 4 := by
    rw [Real.norm_of_nonneg (sq_nonneg ‖t • v‖), norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos]
    dsimp [c]
    field_simp
  rw [hq, hnrm, Real.norm_eq_abs] at he
  have hlo := (abs_le.mp he).1
  nlinarith [mul_pos (sq_pos_of_pos htpos) hv]

/-- A negative quadratic direction excludes a local minimum. -/
theorem exercise31_not_min_of_negative_direction {f : E → ℝ} {a : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : exercise31QuadraticExpansion f a B)
    {v : E} (hv : B v v < 0) : ¬ IsLocalMin f a := by
  have he : exercise31QuadraticExpansion (fun x ↦ -f x) a (-B) := by
    unfold exercise31QuadraticExpansion at hf ⊢
    convert hf.neg_left using 1
    ext h
    simp
    ring
  exact fun hm ↦ exercise31_not_max_of_positive_direction he
    (v := v) (by simpa using hv) hm.neg

/-- Source hypotheses, actual Hessian, and the corrected definite conclusions. -/
theorem exercise31_positive_test [FiniteDimensional ℝ E] {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ 3 f a) (hz : fderiv ℝ f a = 0)
    (hpos : ∀ v ≠ 0, 0 < fderiv ℝ (fderiv ℝ f) a v v) : exercise31StrictMin f a :=
  exercise31_strict_min_of_expansion (exercise31_quadratic_expansion hf hz) hpos

theorem exercise31_negative_test [FiniteDimensional ℝ E] {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ 3 f a) (hz : fderiv ℝ f a = 0)
    (hneg : ∀ v ≠ 0, fderiv ℝ (fderiv ℝ f) a v v < 0) : exercise31StrictMax f a :=
  exercise31_strict_max_of_expansion (exercise31_quadratic_expansion hf hz) hneg

theorem exercise31_indefinite_test {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ 3 f a) (hz : fderiv ℝ f a = 0)
    (hpos : ∃ v, 0 < fderiv ℝ (fderiv ℝ f) a v v)
    (hneg : ∃ v, fderiv ℝ (fderiv ℝ f) a v v < 0) :
    ¬ IsLocalMin f a ∧ ¬ IsLocalMax f a := by
  obtain ⟨v, hv⟩ := hpos
  obtain ⟨w, hw⟩ := hneg
  have he := exercise31_quadratic_expansion hf hz
  exact ⟨exercise31_not_min_of_negative_direction he hw,
    exercise31_not_max_of_positive_direction he hv⟩

/-- A nonzero symmetric semidefinite form has a strictly positive direction. -/
theorem exercise31_semidefinite_direction (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x) (hn : B ≠ 0) :
    ∃ x, 0 < B x x := by
  by_contra h
  push Not at h
  have hz (x : E) : B x x = 0 := le_antisymm (h x) (hp x)
  apply hn
  ext x y
  have he := hz (x + y)
  simp only [map_add, add_apply, hz, hs y x, zero_add, add_zero] at he
  simp only [zero_apply]
  linarith

/-- Even in the singular semidefinite case, the opposite extremum is excluded. -/
theorem exercise31_semidefinite_exclusions {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ 3 f a) (hz : fderiv ℝ f a = 0)
    (hn : fderiv ℝ (fderiv ℝ f) a ≠ 0) :
    ((∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) a v v) → ¬ IsLocalMax f a) ∧
    ((∀ v, fderiv ℝ (fderiv ℝ f) a v v ≤ 0) → ¬ IsLocalMin f a) := by
  let B := fderiv ℝ (fderiv ℝ f) a
  have hfirst : ∀ᶠ x in 𝓝 a, HasFDerivAt f (fderiv ℝ f x) x := by
    filter_upwards [hf.eventually (by norm_num)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasFDerivAt
  have hsecond : HasFDerivAt (fderiv ℝ f) B a :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hs := second_derivative_symmetric_of_eventually_of_real hfirst hsecond
  have he := exercise31_quadratic_expansion hf hz
  constructor
  · intro hp
    obtain ⟨v, hv⟩ := exercise31_semidefinite_direction B hs hp hn
    exact exercise31_not_max_of_positive_direction he hv
  · intro hp
    obtain ⟨v, hv⟩ := exercise31_semidefinite_direction (-B)
      (fun x y ↦ by simpa using congrArg Neg.neg (hs x y))
      (fun x ↦ by simpa using hp x) (neg_ne_zero.mpr hn)
    apply exercise31_not_min_of_negative_direction he (v := v)
    simpa using hv

end QuadraticBounds

/-- The nonzero second derivative is decisive in one real dimension. -/
theorem exercise31_one_dimension {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 3 f a) (hz : fderiv ℝ f a = 0)
    (hn : fderiv ℝ (fderiv ℝ f) a ≠ 0) :
    (0 < fderiv ℝ (fderiv ℝ f) a 1 1 ∧ exercise31StrictMin f a ∧ ¬ IsLocalMax f a) ∨
    (fderiv ℝ (fderiv ℝ f) a 1 1 < 0 ∧ exercise31StrictMax f a ∧ ¬ IsLocalMin f a) := by
  let B := fderiv ℝ (fderiv ℝ f) a
  have he (x y : ℝ) : B x y = x * y * B 1 1 := by
    have hx : B x = x • B 1 := by simpa only [smul_eq_mul, mul_one] using B.map_smul x 1
    have hy : B 1 y = y * B 1 1 := by
      simpa only [smul_eq_mul, mul_one] using (B 1).map_smul y 1
    rw [hx]
    change x * B 1 y = _
    rw [hy]
    ring
  have hn1 : B 1 1 ≠ 0 := by
    intro hh
    apply hn
    change B = 0
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    change B x y = 0
    rw [he, hh, mul_zero]
  have hex := exercise31_quadratic_expansion hf hz
  rcases lt_or_gt_of_ne hn1 with hneg | hpos
  · refine Or.inr ⟨hneg, exercise31_negative_test hf hz ?_,
      exercise31_not_min_of_negative_direction hex hneg⟩
    intro v hv
    change B v v < 0
    rw [he]
    exact mul_neg_of_pos_of_neg (mul_self_pos.mpr hv) hneg
  · refine Or.inl ⟨hpos, exercise31_positive_test hf hz ?_,
      exercise31_not_max_of_positive_direction hex hpos⟩
    intro v hv
    change 0 < B v v
    rw [he]
    exact mul_pos (mul_self_pos.mpr hv) hpos

section Counterexamples

/-- Dimension `n+2` includes the plane and every larger dimension. -/
abbrev Exercise31Space (n : ℕ) := EuclideanSpace ℝ (Fin (n + 2))

def exercise31Counterexample (n : ℕ) (c : ℝ) (p : Exercise31Space n) : ℝ :=
  (∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)), p i ^ 2) + c * p 1 ^ 4

def exercise31CounterDerivative (n : ℕ) (c : ℝ) (p : Exercise31Space n) :
    Exercise31Space n →L[ℝ] ℝ :=
  (∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)),
    (2 * p i) • PiLp.proj 2 (fun _ : Fin (n + 2) ↦ ℝ) i) +
    (c * (4 * p 1 ^ 3)) • PiLp.proj 2 (fun _ : Fin (n + 2) ↦ ℝ) 1

def exercise31CounterHessian (n : ℕ) :
    Exercise31Space n →L[ℝ] Exercise31Space n →L[ℝ] ℝ :=
  ∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)),
    (2 : ℝ) • (PiLp.proj 2 (fun _ : Fin (n + 2) ↦ ℝ) i).smulRight
      (PiLp.proj 2 (fun _ : Fin (n + 2) ↦ ℝ) i)

theorem exercise31_counter_smooth (n : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (exercise31Counterexample n c) := by
  unfold exercise31Counterexample
  fun_prop

theorem exercise31_counter_derivative (n : ℕ) (c : ℝ) (p : Exercise31Space n) :
    HasFDerivAt (exercise31Counterexample n c) (exercise31CounterDerivative n c p) p := by
  have hi (i : Fin (n + 2)) := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p i
  have hs := HasFDerivAt.fun_sum (u := Finset.univ.erase (1 : Fin (n + 2)))
    (fun i _ ↦ (hi i).pow 2)
  have hp := ((hi 1).pow 4).const_mul c
  convert hs.fun_add hp using 1
  · ext q
    rfl
  · simp only [exercise31CounterDerivative, Nat.reduceSub, pow_one, nsmul_eq_mul,
      smul_smul, Nat.cast_ofNat]

theorem exercise31_counter_hessian (n : ℕ) (c : ℝ) :
    HasFDerivAt (fderiv ℝ (exercise31Counterexample n c)) (exercise31CounterHessian n) 0 := by
  have he : fderiv ℝ (exercise31Counterexample n c) = exercise31CounterDerivative n c :=
    funext fun p ↦ (exercise31_counter_derivative n c p).fderiv
  rw [he]
  have hi (i : Fin (n + 2)) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : Exercise31Space n) i
  let pr (i : Fin (n + 2)) : Exercise31Space n →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin (n + 2) ↦ ℝ) i
  have hs := HasFDerivAt.fun_sum (u := Finset.univ.erase (1 : Fin (n + 2)))
    (fun i _ ↦ ((hi i).const_mul 2).smul_const (pr i))
  have hp := (((hi 1).pow 3).const_mul (c * 4)).smul_const (pr 1)
  convert hs.fun_add hp using 1
  · ext p v
    simp [exercise31CounterDerivative, pr, mul_assoc]
  · apply ContinuousLinearMap.ext
    intro p
    apply ContinuousLinearMap.ext
    intro v
    simp only [exercise31CounterHessian, pr, sum_apply,
      add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.proj_apply, PiLp.zero_apply, zero_pow (by decide : 2 ≠ 0),
      smul_zero, zero_smul, zero_apply, add_zero, Nat.reduceSub, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem exercise31_counter_same_jet (n : ℕ) (c : ℝ) :
    exercise31Counterexample n c 0 = 0 ∧
    fderiv ℝ (exercise31Counterexample n c) 0 = 0 ∧
    fderiv ℝ (fderiv ℝ (exercise31Counterexample n c)) 0 = exercise31CounterHessian n := by
  refine ⟨by simp [exercise31Counterexample], ?_, (exercise31_counter_hessian n c).fderiv⟩
  rw [(exercise31_counter_derivative n c 0).fderiv]
  simp [exercise31CounterDerivative]

theorem exercise31_counter_hessian_apply (n : ℕ) (v w : Exercise31Space n) :
    exercise31CounterHessian n v w =
      ∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)), 2 * v i * w i := by
  simp only [exercise31CounterHessian, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exercise31_counter_hessian_nonnegative (n : ℕ) (v : Exercise31Space n) :
    0 ≤ exercise31CounterHessian n v v := by
  rw [exercise31_counter_hessian_apply]
  exact Finset.sum_nonneg fun i _ ↦ by nlinarith [sq_nonneg (v i)]

theorem exercise31_counter_hessian_axis (n : ℕ) :
    exercise31CounterHessian n (PiLp.single 2 0 1) (PiLp.single 2 0 1) = 2 := by
  have hn : (0 : Fin (n + 2)) ≠ 1 := by
    norm_num [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 1 < n + 2)]
  simp [exercise31_counter_hessian_apply, PiLp.single_apply, hn]

theorem exercise31_counter_hessian_nonzero (n : ℕ) : exercise31CounterHessian n ≠ 0 := by
  intro hz
  have h := exercise31_counter_hessian_axis n
  rw [hz] at h
  norm_num at h

theorem exercise31_counter_hessian_kernel (n : ℕ) :
    (PiLp.single 2 1 1 : Exercise31Space n) ≠ 0 ∧
      exercise31CounterHessian n (PiLp.single 2 1 1) = 0 := by
  constructor
  · simp
  · ext w
    simp only [exercise31_counter_hessian_apply, zero_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
    simp [hi1]

/-- The plus sign gives a strict global, hence local, minimum. -/
theorem exercise31_counter_positive (n : ℕ) {p : Exercise31Space n} (hp : p ≠ 0) :
    0 < exercise31Counterexample n 1 p := by
  have hs : 0 ≤ ∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)), p i ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg (p i)
  have hx : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hx
  unfold exercise31Counterexample
  by_cases hi1 : i = 1
  · subst i
    have hpow : 0 < p 1 ^ 4 := by
      simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hi) 2
    nlinarith
  · have hle := Finset.single_le_sum (s := Finset.univ.erase (1 : Fin (n + 2)))
      (f := fun i ↦ p i ^ 2) (fun j _ ↦ sq_nonneg (p j))
      (show i ∈ Finset.univ.erase (1 : Fin (n + 2)) by simp [hi1])
    nlinarith [sq_pos_of_ne_zero hi, sq_nonneg (p 1 ^ 2)]

theorem exercise31_counter_minimum (n : ℕ) :
    exercise31StrictMin (exercise31Counterexample n 1) 0 := by
  refine ⟨1, by norm_num, fun h _ hh ↦ ?_⟩
  simpa [exercise31Counterexample] using exercise31_counter_positive n hh

theorem exercise31_counter_axis_values (n : ℕ) (c t : ℝ) :
    exercise31Counterexample n c (PiLp.single 2 0 t) = t ^ 2 ∧
    exercise31Counterexample n c (PiLp.single 2 1 t) = c * t ^ 4 := by
  have hn : (0 : Fin (n + 2)) ≠ 1 := by
    norm_num [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 1 < n + 2)]
  constructor <;> simp [exercise31Counterexample, PiLp.single_apply, hn, Ne.symm hn]

theorem exercise31_counter_neither (n : ℕ) :
    ¬ IsLocalMin (exercise31Counterexample n (-1)) 0 ∧
    ¬ IsLocalMax (exercise31Counterexample n (-1)) 0 := by
  constructor
  · intro hm
    have hc : Continuous (fun t : ℝ ↦ (PiLp.single 2 1 t : Exercise31Space n)) :=
      (Isometry.of_dist_eq fun x y ↦ PiLp.dist_single_same 2
        (fun _ : Fin (n + 2) ↦ ℝ) 1 x y).continuous
    have hz : (PiLp.single 2 1 (0 : ℝ) : Exercise31Space n) = 0 := by
      exact (PiLp.single_eq_zero_iff 2 1).mpr rfl
    have ht : Tendsto (fun t : ℝ ↦ (PiLp.single 2 1 t : Exercise31Space n))
        (𝓝 0) (𝓝 0) := by simpa only [hz] using hc.tendsto 0
    have he : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ -(t ^ 4) := by
      filter_upwards [ht.eventually hm] with t hh
      simpa only [exercise31_counter_axis_values n (-1) t |>.2,
        exercise31_counter_same_jet n (-1) |>.1, neg_one_mul] using hh
    obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp he
    have htpos : 0 < r / 2 := by positivity
    have hh := hbound (y := r / 2) (by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos htpos]
      linarith)
    linarith [pow_pos htpos 4]
  · have hf : ContDiffAt ℝ 3 (exercise31Counterexample n (-1)) 0 :=
      (exercise31_counter_smooth n (-1)).contDiffAt.of_le (by simp)
    apply exercise31_not_max_of_positive_direction
      (exercise31_quadratic_expansion hf (exercise31_counter_same_jet n (-1)).2.1)
      (v := PiLp.single 2 0 1)
    rw [(exercise31_counter_same_jet n (-1)).2.2, exercise31_counter_hessian_axis]
    norm_num

/-- The actual degree-two Taylor polynomial, including its constant and linear terms. -/
def exercise31QuadraticPolynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (a h : E) : ℝ :=
  f a + fderiv ℝ f a h + fderiv ℝ (fderiv ℝ f) a h h / 2

theorem exercise31_counter_taylor (n : ℕ) (c : ℝ) (h : Exercise31Space n) :
    exercise31QuadraticPolynomial (exercise31Counterexample n c) 0 h =
      ∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)), h i ^ 2 := by
  rw [exercise31QuadraticPolynomial, (exercise31_counter_same_jet n c).1,
    (exercise31_counter_same_jet n c).2.1, (exercise31_counter_same_jet n c).2.2,
    exercise31_counter_hessian_apply]
  simp only [zero_apply, zero_add, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exercise31_counter_gradient (n : ℕ) (c : ℝ) :
    HasGradientAt (exercise31Counterexample n c) 0 0 := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa [exercise31CounterDerivative] using exercise31_counter_derivative n c 0

theorem exercise31_counter_isLocalMin (n : ℕ) :
    IsLocalMin (exercise31Counterexample n 1) 0 := by
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p = 0
  · simp [hp]
  · simpa only [(exercise31_counter_same_jet n 1).1] using
      (exercise31_counter_positive n hp).le

/-- The source obstruction in the plane and in every higher dimension. -/
theorem exercise31_counterexample (n : ℕ) :
    ContDiff ℝ 3 (exercise31Counterexample n 1) ∧
    ContDiff ℝ 3 (exercise31Counterexample n (-1)) ∧
    HasGradientAt (exercise31Counterexample n 1) 0 0 ∧
    HasGradientAt (exercise31Counterexample n (-1)) 0 0 ∧
    fderiv ℝ (fderiv ℝ (exercise31Counterexample n 1)) 0 =
      fderiv ℝ (fderiv ℝ (exercise31Counterexample n (-1))) 0 ∧
    fderiv ℝ (fderiv ℝ (exercise31Counterexample n 1)) 0 ≠ 0 ∧
    (∀ h, exercise31QuadraticPolynomial (exercise31Counterexample n 1) 0 h =
      exercise31QuadraticPolynomial (exercise31Counterexample n (-1)) 0 h) ∧
    exercise31StrictMin (exercise31Counterexample n 1) 0 ∧
    IsLocalMin (exercise31Counterexample n 1) 0 ∧
    ¬ IsLocalMin (exercise31Counterexample n (-1)) 0 ∧
    ¬ IsLocalMax (exercise31Counterexample n (-1)) 0 := by
  refine ⟨(exercise31_counter_smooth n 1).of_le (by simp),
    (exercise31_counter_smooth n (-1)).of_le (by simp),
    exercise31_counter_gradient n 1, exercise31_counter_gradient n (-1), ?_, ?_, ?_,
    exercise31_counter_minimum n, exercise31_counter_isLocalMin n,
    (exercise31_counter_neither n).1, (exercise31_counter_neither n).2⟩
  · rw [(exercise31_counter_same_jet n 1).2.2, (exercise31_counter_same_jet n (-1)).2.2]
  · rw [(exercise31_counter_same_jet n 1).2.2]
    exact exercise31_counter_hessian_nonzero n
  · intro h
    rw [exercise31_counter_taylor, exercise31_counter_taylor]

/-- Negation gives the matching negative-semidefinite examples with genuine jets. -/
theorem exercise31_counter_negative_jet (n : ℕ) (c : ℝ) :
    ContDiff ℝ 3 (fun p ↦ -exercise31Counterexample n c p) ∧
    HasFDerivAt (𝕜 := ℝ) (fun p ↦ -exercise31Counterexample n c p) 0 0 ∧
    fderiv ℝ (fderiv ℝ (fun p ↦ -exercise31Counterexample n c p)) 0 =
      -exercise31CounterHessian n := by
  refine ⟨((exercise31_counter_smooth n c).of_le (by simp)).neg, ?_, ?_⟩
  · simpa [exercise31CounterDerivative] using (exercise31_counter_derivative n c 0).fun_neg
  · have he : fderiv ℝ (fun p ↦ -exercise31Counterexample n c p) =
        fun p ↦ -fderiv ℝ (exercise31Counterexample n c) p := by
      funext p
      rw [(exercise31_counter_derivative n c p).fun_neg.fderiv,
        (exercise31_counter_derivative n c p).fderiv]
    rw [he]
    exact (exercise31_counter_hessian n c).fun_neg.fderiv

theorem exercise31_counter_negative_taylor (n : ℕ) (c : ℝ) (h : Exercise31Space n) :
    exercise31QuadraticPolynomial (fun p ↦ -exercise31Counterexample n c p) 0 h =
      -(∑ i ∈ Finset.univ.erase (1 : Fin (n + 2)), h i ^ 2) := by
  rw [exercise31QuadraticPolynomial, (exercise31_counter_same_jet n c).1,
    (exercise31_counter_negative_jet n c).2.1.fderiv,
    (exercise31_counter_negative_jet n c).2.2]
  simp only [neg_zero, zero_apply, zero_add, neg_apply, neg_div, exercise31_counter_hessian_apply]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exercise31_counter_negative_behavior (n : ℕ) :
    exercise31StrictMax (fun p ↦ -exercise31Counterexample n 1 p) 0 ∧
    ¬ IsLocalMin (fun p ↦ -exercise31Counterexample n (-1) p) 0 ∧
    ¬ IsLocalMax (fun p ↦ -exercise31Counterexample n (-1) p) 0 := by
  obtain ⟨r, hr, hm⟩ := exercise31_counter_minimum n
  refine ⟨⟨r, hr, fun h hh hn ↦ neg_lt_neg (hm h hh hn)⟩, ?_, ?_⟩
  · intro h
    exact (exercise31_counter_neither n).2 (by simpa only [neg_neg] using h.neg)
  · intro h
    exact (exercise31_counter_neither n).1 (by simpa only [neg_neg] using h.neg)

/-- The plane examples are literally `x²+y⁴` and `x²-y⁴`. -/
theorem exercise31_planar_formula (x y c : ℝ) :
    exercise31Counterexample 0 c (WithLp.toLp 2 ![x, y]) = x ^ 2 + c * y ^ 4 := by
  simp [exercise31Counterexample, Fin.sum_univ_two]

/-- Dimension zero admits no nonzero Hessian, so the source hypothesis is impossible. -/
theorem exercise31_zero_dimension (B : EuclideanSpace ℝ (Fin 0) →L[ℝ]
    EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) : B = 0 := by
  ext x y
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

end Counterexamples

end Rudin.Chapter09
