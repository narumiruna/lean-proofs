module

public import Math.Rudin.Support.EuclideanFlux
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Exercise 10.31: Green identities

Source: primary PDF pages 306–307, book pages 297–298. Regions are exactly the
finite positive smooth-simplex unions from Section 10.31. The support module
proves the geometric volume and Gram-area comparisons and derives divergence
from actual local Stokes. No divergence theorem is a hypothesis.

Both identities and harmonic zero flux hold in every positive dimension.
Zero-boundary uniqueness follows from the `g=h` identity, zero energy,
and continuity of the gradient. Functional cancellation uses only the actual
frontier condition. A first-derivative argument handles disconnected compact
regions. A separate second-derivative maximum-principle proof is retained as
an independent result, not as the source's requested energy proof.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10

open Set MeasureTheory
open scoped RealInnerProductSpace
open Rudin.Support.EuclideanFlux

/-- Exercise 31(a), with the actual Euclidean gradient and Fréchet derivative. -/
theorem exercise31_a {U : Set (Space 3)} (hU : IsOpen U)
    {g h : Space 3 → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U)
    {x : Space 3} (hx : x ∈ U) :
    divergence (fun y => g y • gradient h y) x =
      g x * laplacian h x + ⟪gradient g x, gradient h x⟫ :=
  divergence_mul_gradient hU hg hh hx

theorem exercise31_laplacian_continuous {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {h : Space n → ℝ} (hh : ContDiffOn ℝ 2 h U) : ContinuousOn (laplacian h) U :=
  divergence_continuousOn hU (gradient_contDiffOn hU hh)

theorem exercise31_first_integrable {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {g h : Space (n+1) → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    IntegrableOn (fun x => g x * laplacian h x + ⟪gradient g x, gradient h x⟫)
      R.carrier :=
  R.integrableOn (((hg.continuousOn.mul (exercise31_laplacian_continuous hU hh)).add
    ((gradient_contDiffOn hU hg).continuousOn.inner
      (gradient_contDiffOn hU hh).continuousOn)).mono hR)

theorem exercise31_second_integrable {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {g h : Space (n+1) → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    IntegrableOn (fun x => g x * laplacian h x - h x * laplacian g x) R.carrier :=
  R.integrableOn (((hg.continuousOn.mul (exercise31_laplacian_continuous hU hh)).sub
    (hh.continuousOn.mul (exercise31_laplacian_continuous hU hg))).mono hR)

/-- The geometric normal-derivative density on every actual face is integrable. -/
theorem exercise31_boundary_integrable {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {g h : Space (n+1) → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U)
    (c : Fin R.count) (i : Fin (n+2)) :
    IntegrableOn (fun u =>
      g (((R.cell c).simplex.face i).val u) *
        ⟪gradient h (((R.cell c).simplex.face i).val u),
          unitNormal (tangentFrame ((R.cell c).simplex.face i) u)⟫ *
        areaDensity (tangentFrame ((R.cell c).simplex.face i) u))
      (Rudin.Support.SimplexIntegration.standardSimplex n) := by
  simpa only [Pi.smul_apply', inner_smul_left, starRingEnd_apply, star_trivial] using
    R.boundary_flux_integrable hR
      (hg.continuousOn.smul (gradient_contDiffOn hU hh).continuousOn) c i

/-- The first Green identity in every positive dimension. `n=0` is the
one-dimensional identity with its two endpoint faces. -/
theorem exercise31_first_green {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {g h : Space (n+1) → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    (∫ x in R.carrier, g x * laplacian h x + ⟪gradient g x, gradient h x⟫) =
      R.boundaryIntegral (fun x ν => g x * ⟪gradient h x, ν⟫) := by
  have hd := R.divergence_integral hU hR (fun x => g x • gradient h x)
    ((hg.of_le (by norm_num)).smul (gradient_contDiffOn hU hh))
  rw [setIntegral_congr_fun R.compact.measurableSet
    (fun x hx => divergence_mul_gradient hU hg hh (hR hx))] at hd
  simpa only [inner_smul_left, starRingEnd_apply, star_trivial] using hd

/-- Subtraction is applied only after integrability of both terms is proved. -/
theorem exercise31_second_green {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {g h : Space (n+1) → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    (∫ x in R.carrier, g x * laplacian h x - h x * laplacian g x) =
      R.boundaryIntegral (fun x ν => g x * ⟪gradient h x, ν⟫ -
        h x * ⟪gradient g x, ν⟫) := by
  have he := congrArg₂ (fun a b : ℝ => a - b)
    (exercise31_first_green R hU hR hg hh) (exercise31_first_green R hU hR hh hg)
  rw [← integral_sub (exercise31_first_integrable R hU hR hg hh)
    (exercise31_first_integrable R hU hR hh hg)] at he
  have hc (x : Space (n+1)) :
      (g x * laplacian h x + ⟪gradient g x, gradient h x⟫) -
        (h x * laplacian g x + ⟪gradient h x, gradient g x⟫) =
          g x * laplacian h x - h x * laplacian g x := by
    rw [real_inner_comm (gradient h x)]
    ring
  simp_rw [hc] at he
  have hb := R.boundaryIntegral_flux_sub hR
    (hg.continuousOn.smul (gradient_contDiffOn hU hh).continuousOn)
    (hh.continuousOn.smul (gradient_contDiffOn hU hg).continuousOn)
  simp only [Pi.smul_apply', inner_smul_left, starRingEnd_apply, star_trivial] at hb
  exact he.trans hb.symm

/-- A harmonic function has zero total normal flux. -/
theorem exercise31_harmonic_zero_flux {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {h : Space (n+1) → ℝ} (hh : ContDiffOn ℝ 2 h U)
    (harmonic : ∀ x ∈ U, laplacian h x = 0) :
    R.boundaryIntegral (fun x ν => ⟪gradient h x, ν⟫) = 0 := by
  have he := exercise31_first_green R hU hR (contDiffOn_const (c := (1 : ℝ))) hh
  simp only [gradient_fun_const, inner_zero_left, one_mul, add_zero] at he
  rw [setIntegral_congr_fun R.compact.measurableSet (fun x hx => harmonic x (hR hx)),
    integral_zero] at he
  exact he.symm

/-- Taking `g=h` gives the literal Dirichlet energy identity. -/
theorem exercise31_harmonic_energy {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {h : Space (n+1) → ℝ} (hh : ContDiffOn ℝ 2 h U)
    (harmonic : ∀ x ∈ U, laplacian h x = 0) :
    (∫ x in R.carrier, ‖gradient h x‖ ^ 2) =
      R.boundaryIntegral (fun x ν => h x * ⟪gradient h x, ν⟫) := by
  have he := exercise31_first_green R hU hR hh hh
  rw [setIntegral_congr_fun R.compact.measurableSet
    (fun x hx => by rw [harmonic x (hR hx), mul_zero, zero_add,
      real_inner_self_eq_norm_sq])] at he
  exact he

/-- Existence of the normal directional derivative, not only equality of total operators. -/
theorem exercise31_normal_derivative {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {h : Space n → ℝ} (hh : ContDiffOn ℝ 2 h U) {x : Space n} (hx : x ∈ U)
    (ν : Space n) :
    HasDerivAt (fun t : ℝ => h (x + t • ν)) ⟪gradient h x, ν⟫ 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add x
  have hf := ((hh x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hf' : HasFDerivAt h (fderiv ℝ h x) (x + (0 : ℝ) • ν) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  simpa only [Function.comp_def, inner_gradient_left] using hf'.comp_hasDerivAt 0 hl

/-- The one-variable second derivative test, stated with genuine C² regularity. -/
private theorem second_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hc : ContinuousAt (deriv (deriv f)) x :=
    ((hf.derivWithin (m := 1) (by norm_num)).derivWithin (m := 0) (by norm_num)).continuousAt
  have he : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y ∧
      0 < deriv (deriv f) y ∧ f y ≤ f x :=
    (hf.eventually (by norm_num)).and ((hc.eventually (lt_mem_nhds hp)).and hm)
  obtain ⟨ε, hε, hsub⟩ := Metric.eventually_nhds_iff_ball.mp he
  let a := x - ε / 2
  let b := x + ε / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hx : ∀ y ∈ Icc a b, dist y x < ε := by
    intro y hy
    rw [Real.dist_eq, abs_lt]
    dsimp [a, b] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hs : StrictConvexOn ℝ (Icc a b) f := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc a b)
      (fun y hy => (hsub y (hx y hy)).1.continuousAt.continuousWithinAt)
    intro y hy
    exact (hsub y (hx y (interior_subset hy))).2.1
  have hi := hs.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
    (ne_of_lt hab) (show (0 : ℝ) < 1/2 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)
    (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  have hmida : (1/2 : ℝ) • a + (1/2 : ℝ) • b = x := by dsimp [a,b]; ring
  rw [hmida] at hi
  have ha := (hsub a (hx a (left_mem_Icc.mpr hab.le))).2.2
  have hb := (hsub b (hx b (right_mem_Icc.mpr hab.le))).2.2
  simp only [smul_eq_mul] at hi
  linarith

private theorem gradient_contDiffAt {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (gradient f) x :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.contDiff.contDiffAt.comp x
    (hf.fderiv_right (by norm_num))

/-- The second derivative on a line is the corresponding actual Hessian entry. -/
private theorem line_second {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (v : Space n) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      ⟪fderiv ℝ (gradient f) x v, v⟫ := by
  have hl (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have ht : Filter.Tendsto (fun t : ℝ => x + t • v) (nhds 0) (nhds x) := by
    have hh := (hl 0).continuousAt.tendsto
    simpa only [zero_smul, add_zero] using hh
  have he : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[nhds 0]
      (fun t : ℝ => ⟪gradient f (x + t • v), v⟫) := by
    filter_upwards [ht.eventually (hf.eventually (by norm_num))] with t htf
    simpa only [Function.comp_def, inner_gradient_left] using
      ((htf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hg := ((gradient_contDiffAt hf).differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hg
  have hc := (hg'.comp_hasDerivAt (0 : ℝ) (hl 0)).inner ℝ (hasDerivAt_const (0 : ℝ) v)
  simp only [inner_zero_right, zero_add, Function.comp_def] at hc
  exact (hc.congr_of_eventuallyEq he).deriv

/-- The Laplacian is the sum of actual second derivatives on Cartesian lines. -/
theorem exercise31_laplacian_coordinates {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = ∑ i : Fin n,
      deriv (deriv (fun t : ℝ => f (x + t • EuclideanSpace.single i 1))) 0 := by
  unfold laplacian divergence
  apply Finset.sum_congr rfl
  intro i _
  rw [line_second hf, real_inner_comm]

private theorem laplacian_nonpos_of_localMax {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : laplacian f x ≤ 0 := by
  unfold laplacian divergence
  apply Finset.sum_nonpos
  intro i _
  let v : Space n := EuclideanSpace.single i 1
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => f (x + t • v)) 0 := by
    have hf' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using hf
    exact hf'.comp 0 (by fun_prop)
  have ht : Filter.Tendsto (fun t : ℝ => x + t • v) (nhds 0) (nhds x) := by
    have hc' : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc'.tendsto
  have hm' : IsLocalMax (fun t : ℝ => f (x + t • v)) 0 := by
    change ∀ᶠ t in nhds 0, f (x + t • v) ≤ f (x + (0 : ℝ) • v)
    rw [zero_smul, add_zero]
    exact ht.eventually hm
  have hn := second_nonpos_of_localMax hc hm'
  rw [line_second hf v, real_inner_comm] at hn
  exact hn

private theorem perturb_gradient {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (ε : ℝ) :
    gradient (fun y => f y + ε * ‖y‖ ^ 2) x = gradient f x + (2 * ε) • x := by
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  rw [toDual_gradient, map_add, map_smul, toDual_gradient]
  have hd := hf.hasFDerivAt.fun_add (((hasFDerivAt_id x).norm_sq).const_mul ε)
  simp only [id_eq] at hd
  rw [hd.fderiv]
  ext v
  simp [InnerProductSpace.toDual_apply_apply]
  ring

private theorem perturb_laplacian {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (ε : ℝ) :
    laplacian (fun y => f y + ε * ‖y‖ ^ 2) x = laplacian f x + 2 * ε * n := by
  have he : gradient (fun y => f y + ε * ‖y‖ ^ 2) =ᶠ[nhds x]
      (fun y => gradient f y + (2 * ε) • y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact perturb_gradient (hy.differentiableAt (by norm_num)) ε
  unfold laplacian divergence
  rw [he.fderiv_eq]
  have hd := ((gradient_contDiffAt hf).differentiableAt (by norm_num)).hasFDerivAt.fun_add
    ((hasFDerivAt_id x).const_smul (2 * ε))
  simp only [Pi.smul_apply, id_eq] at hd
  rw [hd.fderiv]
  simp [inner_add_right, inner_smul_right, EuclideanSpace.inner_single_left,
    Finset.sum_add_distrib, mul_assoc]
  ring

/-- A strictly positive Laplacian rules out an interior maximum. -/
private theorem maximum_on_frontier {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hf : ContinuousOn f K)
    (hd : ∀ x ∈ interior K, ContDiffAt ℝ 2 f x ∧ 0 < laplacian f x)
    {x : Space n} (hx : x ∈ K) :
    ∃ y ∈ frontier K, f x ≤ f y := by
  obtain ⟨y, hy, hm⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hf
  refine ⟨y, ⟨subset_closure hy, ?_⟩, hm hx⟩
  intro hi
  have hn := laplacian_nonpos_of_localMax (hd y hi).1
    (hm.isLocalMax (mem_interior_iff_mem_nhds.mp hi))
  linarith [(hd y hi).2]

/-- Compact-domain uniqueness needs neither connectedness nor an inference from
almost-everywhere vanishing. All local maxima are handled by genuine derivatives. -/
theorem exercise31_harmonic_zero_boundary_maximum {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {h : Space (n+1) → ℝ} (hh : ContDiffOn ℝ 2 h U)
    (harmonic : ∀ x ∈ U, laplacian h x = 0)
    (boundary : ∀ x ∈ frontier R.carrier, h x = 0) :
    ∀ x ∈ R.carrier, h x = 0 := by
  have hupper : ∀ (f : Space (n+1) → ℝ), ContDiffOn ℝ 2 f U →
      (∀ x ∈ U, laplacian f x = 0) → (∀ x ∈ frontier R.carrier, f x = 0) →
      ∀ x ∈ R.carrier, f x ≤ 0 := by
    intro f hf hz hb x hx
    obtain ⟨M, hM⟩ := R.compact.bddAbove_image
      (show ContinuousOn (fun y : Space (n+1) => ‖y‖ ^ 2) R.carrier by fun_prop)
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / (|M| + 1)
    have hε : 0 < ε := div_pos hδ (by positivity)
    obtain ⟨y, hy, hxy⟩ := maximum_on_frontier R.compact
      (f := fun y => f y + ε * ‖y‖ ^ 2)
      ((hf.continuousOn.mono hR).add (by fun_prop))
      (fun y hy => ⟨((hf y (hR (interior_subset hy))).contDiffAt
        (hU.mem_nhds (hR (interior_subset hy)))).add
        (contDiffAt_const.mul (contDiffAt_id.norm_sq (𝕜 := ℝ))), by
          rw [perturb_laplacian ((hf y (hR (interior_subset hy))).contDiffAt
            (hU.mem_nhds (hR (interior_subset hy)))), hz y (hR (interior_subset hy))]
          positivity⟩) hx
    rw [hb y hy] at hxy
    have hym : ‖y‖ ^ 2 ≤ M := hM (mem_image_of_mem _ (R.compact.isClosed.frontier_subset hy))
    have heM : ε * M ≤ δ := by
      have hMp : 0 < |M| + 1 := by positivity
      dsimp [ε]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hMp).mpr
      nlinarith [le_abs_self M]
    nlinarith [sq_nonneg ‖x‖, mul_nonneg hε.le (sq_nonneg ‖x‖)]
  intro x hx
  apply le_antisymm (hupper h hh harmonic boundary x hx)
  have hn := hupper (fun x => -h x) hh.neg ?_ (fun x hx => by rw [boundary x hx]; simp) x hx
  · simpa using hn
  · intro y hy
    have hg : gradient (fun x => -h x) = fun x => -gradient h x := by
      funext x
      simp [gradient, fderiv_fun_neg]
    simp only [laplacian, divergence, hg, fderiv_fun_neg, _root_.neg_apply,
      inner_neg_right, Finset.sum_neg_distrib]
    exact neg_eq_zero.mpr (harmonic y hy)

/-- The source's first identity in Euclidean three-space. -/
theorem exercise31_b_first (R : Region 3) {U : Set (Space 3)}
    (hU : IsOpen U) (hR : R.carrier ⊆ U) {g h : Space 3 → ℝ}
    (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    (∫ x in R.carrier, g x * laplacian h x + ⟪gradient g x, gradient h x⟫) =
      R.boundaryIntegral (fun x ν => g x * ⟪gradient h x, ν⟫) :=
  exercise31_first_green R hU hR hg hh

/-- The source's second identity in Euclidean three-space. -/
theorem exercise31_b_second (R : Region 3) {U : Set (Space 3)}
    (hU : IsOpen U) (hR : R.carrier ⊆ U) {g h : Space 3 → ℝ}
    (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    (∫ x in R.carrier, g x * laplacian h x - h x * laplacian g x) =
      R.boundaryIntegral (fun x ν => g x * ⟪gradient h x, ν⟫ - h x * ⟪gradient g x, ν⟫) :=
  exercise31_second_green R hU hR hg hh

/-- Both Green identities in every positive dimension, including one.
The successor index encodes exactly the positive dimensions, not only `n=3`. -/
theorem exercise31_d (n : ℕ) (R : Region (n+1)) {U : Set (Space (n+1))}
    (hU : IsOpen U) (hR : R.carrier ⊆ U) {g h : Space (n+1) → ℝ}
    (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) :
    ((∫ x in R.carrier, g x * laplacian h x + ⟪gradient g x, gradient h x⟫) =
      R.boundaryIntegral (fun x ν => g x * ⟪gradient h x, ν⟫)) ∧
    ((∫ x in R.carrier, g x * laplacian h x - h x * laplacian g x) =
      R.boundaryIntegral (fun x ν => g x * ⟪gradient h x, ν⟫ - h x * ⟪gradient g x, ν⟫)) :=
  ⟨exercise31_first_green R hU hR hg hh, exercise31_second_green R hU hR hg hh⟩


/-- The literal `g=h` identity has zero right side under the actual frontier
condition. Internal face values need not vanish. -/
theorem exercise31_energy_zero {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {h : Space (n+1) → ℝ} (hh : ContDiffOn ℝ 2 h U)
    (harmonic : ∀ x ∈ U, laplacian h x = 0)
    (boundary : ∀ x ∈ frontier R.carrier, h x = 0) :
    (∫ x in R.carrier, ‖gradient h x‖ ^ 2) = 0 := by
  rw [exercise31_harmonic_energy R hU hR hh harmonic]
  have hz := R.boundary_flux_zero_of_frontier hU hR
    ((hh.of_le (by norm_num)).smul (gradient_contDiffOn hU hh))
    (fun x hx => by simp [Pi.smul_apply', boundary x hx])
  simpa only [Pi.smul_apply', inner_smul_left, starRingEnd_apply, star_trivial] using hz

/-- Continuity upgrades zero energy to pointwise zero gradient in the interior. -/
theorem exercise31_gradient_zero_of_energy {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {h : Space (n+1) → ℝ} (hh : ContDiffOn ℝ 2 h U)
    (energy : (∫ x in R.carrier, ‖gradient h x‖ ^ 2) = 0) :
    ∀ x ∈ interior R.carrier, gradient h x = 0 := by
  have hc : ContinuousOn (fun x => ‖gradient h x‖ ^ 2) R.carrier :=
    (((gradient_contDiffOn hU hh).continuousOn.norm).pow 2).mono hR
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖gradient h x‖)
    (R.integrableOn hc)).mp energy
  have he := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset interior_subset ha) isOpen_interior
    (hc.mono interior_subset) continuousOn_const
  intro x hx
  have hz : ‖gradient h x‖ ^ 2 = 0 := he hx
  exact norm_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp hz)

/-- A first-derivative argument on a compact set. No connectedness assumption,
second-derivative maximum principle, or harmonic uniqueness theorem is used. -/
theorem zero_of_fderiv_zero_of_frontier {n : ℕ} {K : Set (Space (n+1))}
    (hK : IsCompact K) {f : Space (n+1) → ℝ} (hf : ContinuousOn f K)
    (hd : ∀ x ∈ interior K, DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0)
    (hb : ∀ x ∈ frontier K, f x = 0) : ∀ x ∈ K, f x = 0 := by
  let e : Space (n+1) := EuclideanSpace.single 0 1
  let L : Space (n+1) →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Space (n+1)) e
  have hLe : L e = 1 := by simp [L, e, InnerProductSpace.toDual_apply_apply]
  have hu : ∀ (g : Space (n+1) → ℝ), ContinuousOn g K →
      (∀ x ∈ interior K, DifferentiableAt ℝ g x ∧ fderiv ℝ g x = 0) →
      (∀ x ∈ frontier K, g x = 0) → ∀ x ∈ K, g x ≤ 0 := by
    intro g hg hgd hgb x hx
    obtain ⟨M, hM⟩ := hK.bddAbove_image (L.continuous.norm.continuousOn)
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / (2 * (|M| + 1))
    have hε : 0 < ε := div_pos hδ (by positivity)
    obtain ⟨y, hy, hm⟩ := hK.exists_isMaxOn ⟨x, hx⟩
      (hg.add (continuousOn_const.mul L.continuous.continuousOn))
      (f := fun y => g y + ε * L y)
    have hfront : y ∈ frontier K := by
      refine ⟨subset_closure hy, ?_⟩
      intro hi
      have hlocal := hm.isLocalMax (mem_interior_iff_mem_nhds.mp hi)
      have hd' := (hgd y hi).1.hasFDerivAt.fun_add (L.hasFDerivAt.const_mul ε)
      have heq := congrArg (fun A : Space (n+1) →L[ℝ] ℝ => A e)
        (hlocal.hasFDerivAt_eq_zero hd')
      simp only [(hgd y hi).2, zero_add, _root_.smul_apply, hLe, smul_eq_mul,
        mul_one, _root_.zero_apply] at heq
      linarith
    have hxy : g x + ε * L x ≤ g y + ε * L y := hm hx
    rw [hgb y hfront] at hxy
    have hyM : |L y| ≤ M := hM (mem_image_of_mem _ hy)
    have hxM : |L x| ≤ M := hM (mem_image_of_mem _ hx)
    have heM : ε * (2 * M) ≤ δ := by
      dsimp [ε]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (|M| + 1))).mpr
      nlinarith [le_abs_self M]
    have hxyM : L y - L x ≤ 2 * M := by
      linarith [le_abs_self (L y), neg_abs_le (L x)]
    have := mul_le_mul_of_nonneg_left hxyM hε.le
    linarith
  intro x hx
  apply le_antisymm (hu f hf hd hb x hx)
  have hn := hu (fun x => -f x) hf.neg
    (fun x hx => ⟨(hd x hx).1.neg, by rw [fderiv_fun_neg, (hd x hx).2, neg_zero]⟩)
    (fun x hx => by rw [hb x hx, neg_zero]) x hx
  simpa using hn

theorem exercise31_harmonic_zero_boundary {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {h : Space (n+1) → ℝ} (hh : ContDiffOn ℝ 2 h U)
    (harmonic : ∀ x ∈ U, laplacian h x = 0)
    (boundary : ∀ x ∈ frontier R.carrier, h x = 0) :
    ∀ x ∈ R.carrier, h x = 0 := by
  have hz := exercise31_gradient_zero_of_energy R hU hR hh
    (exercise31_energy_zero R hU hR hh harmonic boundary)
  apply zero_of_fderiv_zero_of_frontier R.compact (hh.continuousOn.mono hR) _ boundary
  intro x hx
  refine ⟨((hh x (hR (interior_subset hx))).contDiffAt
    (hU.mem_nhds (hR (interior_subset hx)))).differentiableAt (by norm_num), ?_⟩
  rw [← toDual_gradient, hz x hx, map_zero]


end Rudin.Chapter10
