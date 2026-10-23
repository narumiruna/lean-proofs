module

public import Math.Rudin.Chapter10.Exercise24
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Chapter 10, Exercise 25

Paths used in the construction are globally C² and constant before zero and
after one. Their C² joins are sums of C² maps, not unproved piecewise joins.
The internal construction only needs zero periods on these closed C² paths;
the source hypothesis for all closed C¹ curves implies this condition.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise25
open Set Filter Topology MeasureTheory
open Rudin.Support
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A C² path, hence a genuine C¹ path, extended constantly outside its interval. -/
structure FlatPath (U : Set V) (x y : V) where
  toFun : ℝ → V
  smooth : ContDiff ℝ 2 toFun
  initial : ∀ t ≤ 0, toFun t = x
  terminal : ∀ t, 1 ≤ t → toFun t = y
  image : ∀ t, toFun t ∈ U

namespace FlatPath
variable {U : Set V} {x y z : V}

@[simp] theorem at_zero (γ : FlatPath U x y) : γ.toFun 0 = x := γ.initial 0 le_rfl
@[simp] theorem at_one (γ : FlatPath U x y) : γ.toFun 1 = y := γ.terminal 1 le_rfl

def refl (hx : x ∈ U) : FlatPath U x x where
  toFun := fun _ => x
  smooth := contDiff_const
  initial := fun _ _ => rfl
  terminal := fun _ _ => rfl
  image := fun _ => hx

def reverse (γ : FlatPath U x y) : FlatPath U y x where
  toFun := fun t => γ.toFun (1-t)
  smooth := γ.smooth.comp (contDiff_const.sub contDiff_id)
  initial := fun t ht => γ.terminal _ (by linarith)
  terminal := fun t ht => γ.initial _ (by linarith)
  image := fun _ => γ.image _

/-- The constant extensions turn concatenation into a globally C² sum. -/
def join (γ : FlatPath U x y) (η : FlatPath U y z) : FlatPath U x z where
  toFun := fun t => γ.toFun (2*t) + η.toFun (2*t-1) - y
  smooth := ((γ.smooth.comp (contDiff_const.mul contDiff_id)).add
    (η.smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))).sub contDiff_const
  initial := by
    intro t ht
    rw [γ.initial _ (by linarith), η.initial _ (by linarith)]
    abel
  terminal := by
    intro t ht
    rw [γ.terminal _ (by linarith), η.terminal _ (by linarith)]
    abel
  image := by
    intro t
    by_cases ht : t ≤ 1/2
    · rw [η.initial _ (by linarith), add_sub_cancel_right]
      exact γ.image _
    · rw [γ.terminal _ (by linarith), add_sub_cancel_left]
      exact η.image _

theorem join_left (γ : FlatPath U x y) (η : FlatPath U y z) {t : ℝ} (ht : t ≤ 1/2) :
    (γ.join η).toFun t = γ.toFun (2*t) := by
  simp only [join, η.initial _ (by linarith : 2*t-1 ≤ 0), add_sub_cancel_right]

theorem join_right (γ : FlatPath U x y) (η : FlatPath U y z) {t : ℝ} (ht : 1/2 ≤ t) :
    (γ.join η).toFun t = η.toFun (2*t-1) := by
  simp only [join, γ.terminal _ (by linarith : 1 ≤ 2*t), add_sub_cancel_left]

/-- Smooth flattening of an affine segment, with no change in its image. -/
def segment (hc : Convex ℝ U) (hx : x ∈ U) (hy : y ∈ U) : FlatPath U x y where
  toFun := fun t => Exercise24.line x y (Real.smoothTransition t)
  smooth := by
    unfold Exercise24.line OrientedChains.Parametric.segment
    exact ((contDiff_const.sub Real.smoothTransition.contDiff).smul contDiff_const).add
      (Real.smoothTransition.contDiff.smul contDiff_const)
  initial := by
    intro t ht
    simp [Real.smoothTransition.zero_of_nonpos ht, Exercise24.line,
      OrientedChains.Parametric.segment]
  terminal := by
    intro t ht
    simp [Real.smoothTransition.one_of_one_le ht, Exercise24.line,
      OrientedChains.Parametric.segment]
  image := fun t => Exercise24.line_mem hc hx hy
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

def integral (ω : PathIntegration.OneForm V) (γ : FlatPath U x y) : ℝ :=
  PathIntegration.pathIntegral ω γ.toFun

theorem coefficient_continuous {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U)
    (γ : FlatPath U x y) : Continuous (PathIntegration.coefficient ω γ.toFun) :=
  (hω.comp_continuous γ.smooth.continuous γ.image).clm_apply
    (γ.smooth.continuous_deriv (by norm_num))

theorem source {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) (γ : FlatPath U x y) :
    StieltjesPrototype.HasDarbouxRSIntegral (PathIntegration.coefficient ω γ.toFun) id 0 1
      (γ.integral ω) :=
  PathIntegration.darboux_path_bridge ω γ.toFun (coefficient_continuous hω γ).continuousOn

theorem integral_reverse (ω : PathIntegration.OneForm V) (γ : FlatPath U x y) :
    γ.reverse.integral ω = -γ.integral ω :=
  PathIntegration.pathIntegral_reverse ω γ.toFun

theorem integral_join {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U)
    (γ : FlatPath U x y) (η : FlatPath U y z) :
    (γ.join η).integral ω = γ.integral ω + η.integral ω := by
  have hd (p : FlatPath U x y) (t : ℝ) :=
    (p.smooth.differentiable (by norm_num) t).hasDerivAt
  have hl : (∫ t in (0 : ℝ)..(1/2), PathIntegration.coefficient ω (γ.join η).toFun t) =
      γ.integral ω := by
    have he : (∫ t in (0 : ℝ)..(1/2), PathIntegration.coefficient ω (γ.join η).toFun t) =
        ∫ t in (0 : ℝ)..(1/2), 2 * PathIntegration.coefficient ω γ.toFun (2*t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have hg : (γ.join η).toFun =ᶠ[𝓝 t] fun s => γ.toFun (2*s) := by
        filter_upwards [Iio_mem_nhds ht.2] with s hs
        exact join_left γ η hs.le
      have hh := (hd γ (2*t)).scomp t ((hasDerivAt_id t).const_mul 2)
      simp only [Function.comp_def, mul_one] at hh
      simp only [PathIntegration.coefficient, hg.eq_of_nhds, hg.deriv_eq, hh.deriv,
        map_smul, smul_eq_mul]
    rw [he, intervalIntegral.integral_const_mul]
    simpa only [integral, PathIntegration.pathIntegral, mul_zero, mul_one_div_cancel
      (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul] using
      intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1/2)
        (PathIntegration.coefficient ω γ.toFun) 2
  have hr : (∫ t in (1/2 : ℝ)..1, PathIntegration.coefficient ω (γ.join η).toFun t) =
      η.integral ω := by
    have he : (∫ t in (1/2 : ℝ)..1, PathIntegration.coefficient ω (γ.join η).toFun t) =
        ∫ t in (1/2 : ℝ)..1, (PathIntegration.coefficient ω η.toFun) (2*t-1) * 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have hg : (γ.join η).toFun =ᶠ[𝓝 t] fun s => η.toFun (2*s-1) := by
        filter_upwards [Ioi_mem_nhds ht.1] with s hs
        exact join_right γ η hs.le
      have hh := ((η.smooth.differentiable (by norm_num) (2*t-1)).hasDerivAt).scomp t
        (((hasDerivAt_id t).const_mul 2).sub_const 1)
      simp only [Function.comp_def, id_eq, mul_one] at hh
      simp only [PathIntegration.coefficient, hg.eq_of_nhds, hg.deriv_eq]
      rw [hh.deriv]
      simp only [map_smul, smul_eq_mul, mul_comm]
    rw [he]
    have hs := intervalIntegral.integral_comp_mul_deriv (a := (1/2 : ℝ)) (b := 1)
      (fun t _ => (((hasDerivAt_id t).const_mul 2).sub_const 1)) continuous_const.continuousOn
      (coefficient_continuous hω η)
    norm_num only [Function.comp_def, id_eq, mul_one, mul_one_div_cancel
      (by norm_num : (2 : ℝ) ≠ 0), sub_self, show (2 : ℝ)-1=1 by norm_num] at hs
    exact hs
  have hi := (coefficient_continuous hω (γ.join η))
  exact (intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable 0 (1/2))
    (hi.intervalIntegrable (1/2) 1)).symm.trans (congrArg₂ (· + ·) hl hr)

/-- Flattening preserves the actual segment integral by substitution. -/
theorem integral_segment {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U)
    (hc : Convex ℝ U) (hx : x ∈ U) (hy : y ∈ U) :
    (segment hc hx hy).integral ω = Exercise24.segmentIntegral ω x y := by
  have hd := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have he : (segment hc hx hy).integral ω = ∫ t in (0 : ℝ)..1,
      (fun s => ω (Exercise24.line x y s) (y-x)) (Real.smoothTransition t) *
        deriv Real.smoothTransition t := by
    apply intervalIntegral.integral_congr
    intro t _
    have hh := (PathIntegration.segment_hasDerivAt x y (Real.smoothTransition t)).scomp t
      (hd t).hasDerivAt
    simp only [Function.comp_def] at hh
    change ω (Exercise24.line x y (Real.smoothTransition t))
      (deriv (fun s => Exercise24.line x y (Real.smoothTransition s)) t) = _
    rw [hh.deriv, map_smul]
    simp only [smul_eq_mul, mul_comm]
  rw [he]
  have hs := intervalIntegral.integral_comp_mul_deriv' (a := (0 : ℝ)) (b := 1)
    (fun t _ => (hd t).hasDerivAt)
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)).continuousOn
    ((Exercise24.segment_coefficient_continuous hω hc hx hy).mono (by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩))
  simpa only [Real.smoothTransition.zero, Real.smoothTransition.one,
    Function.comp_def, Exercise24.segmentIntegral] using hs

/-- Change only the target set, not the map or derivative. -/
def mono {W : Set V} (γ : FlatPath U x y) (hUW : U ⊆ W) : FlatPath W x y where
  toFun := γ.toFun
  smooth := γ.smooth
  initial := γ.initial
  terminal := γ.terminal
  image := fun t => hUW (γ.image t)

end FlatPath

/-- A C¹ curve on the compact unit interval, with genuine one-sided endpoint
 derivatives. No ambient endpoint derivative is required. -/
structure C1Curve (U : Set V) where
  toFun : ℝ → V
  velocity : ℝ → V
  continuous : ContinuousOn toFun (Icc 0 1)
  continuous_velocity : ContinuousOn velocity (Icc 0 1)
  derivative : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt toFun (velocity t) (Icc 0 1) t
  image : MapsTo toFun (Icc (0 : ℝ) 1) U

def C1Curve.integral {U : Set V} (γ : C1Curve U) (ω : PathIntegration.OneForm V) : ℝ :=
  ∫ t in (0 : ℝ)..1, ω (γ.toFun t) (γ.velocity t)

def FlatPath.toCurve {U : Set V} {x y : V} (γ : FlatPath U x y) : C1Curve U where
  toFun := γ.toFun
  velocity := deriv γ.toFun
  continuous := γ.smooth.continuous.continuousOn
  continuous_velocity := (γ.smooth.continuous_deriv (by norm_num)).continuousOn
  derivative := fun t _ => (γ.smooth.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt
  image := fun t _ => γ.image t

/-- The source assumption applies to every closed C¹ curve, not merely to
 polygonal curves or to closed chains. -/
def ClosedIntegralsVanish (ω : PathIntegration.OneForm V) (U : Set V) : Prop :=
  ∀ γ : C1Curve U, γ.toFun 0 = γ.toFun 1 → γ.integral ω = 0

/-- The internal period condition tests only genuine closed C² paths. -/
def FlatClosedIntegralsVanish (ω : PathIntegration.OneForm V) (U : Set V) : Prop :=
  ∀ x : V, ∀ γ : FlatPath U x x, γ.integral ω = 0

theorem ClosedIntegralsVanish.flat {U : Set V} {ω : PathIntegration.OneForm V}
    (hz : ClosedIntegralsVanish ω U) : FlatClosedIntegralsVanish ω U := by
  intro x γ
  exact hz γ.toCurve (by change γ.toFun 0 = γ.toFun 1; rw [γ.at_zero, γ.at_one])

/-- Path independence follows from a genuine C² closed join. -/
theorem path_independence {U : Set V} {ω : PathIntegration.OneForm V}
    (hω : ContinuousOn ω U) (hz : FlatClosedIntegralsVanish ω U)
    {x y : V} (γ η : FlatPath U x y) : γ.integral ω = η.integral ω := by
  have h := hz x (γ.join η.reverse)
  rw [FlatPath.integral_join hω, FlatPath.integral_reverse] at h
  linarith

/-- Path independence under the original closed-C¹-curve hypothesis. -/
theorem path_independence_of_closed {U : Set V} {ω : PathIntegration.OneForm V}
    (hω : ContinuousOn ω U) (hz : ClosedIntegralsVanish ω U)
    {x y : V} (γ η : FlatPath U x y) : γ.integral ω = η.integral ω :=
  path_independence hω hz.flat γ η

/-- Reachability by the flattened C¹ paths is an equivalence relation. -/
def pathSetoid (U : Set V) : Setoid U where
  r x y := Nonempty (FlatPath U x.val y.val)
  iseqv := ⟨fun x => ⟨FlatPath.refl x.property⟩,
    fun ⟨γ⟩ => ⟨γ.reverse⟩, fun ⟨γ⟩ ⟨η⟩ => ⟨γ.join η⟩⟩

/-- Choose one base point for each component, not one base point for all of U. -/
def base {U : Set V} (x : U) : U := (Quotient.mk (pathSetoid U) x).out

theorem base_related {U : Set V} (x : U) : Nonempty (FlatPath U (base x).val x.val) :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (pathSetoid U) x))

theorem base_eq {U : Set V} {x y : U} (γ : FlatPath U x.val y.val) : base x = base y :=
  congrArg Quotient.out (Quotient.sound (s := pathSetoid U) ⟨γ⟩)

def chosenPath {U : Set V} (x : U) : FlatPath U (base x).val x.val :=
  Classical.choice (base_related x)

/-- The potential uses the path from the chosen base of the point's component.
 Its extension off U is irrelevant to all local derivatives. -/
def potential (ω : PathIntegration.OneForm V) (U : Set V) (x : V) : ℝ := by
  classical
  exact if hx : x ∈ U then (chosenPath ⟨x,hx⟩).integral ω else 0

theorem potential_increment {U : Set V} {ω : PathIntegration.OneForm V}
    (hω : ContinuousOn ω U) (hz : FlatClosedIntegralsVanish ω U)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) (γ : FlatPath U x y) :
    potential ω U y - potential ω U x = γ.integral ω := by
  have hb := base_eq (x := ⟨x,hx⟩) (y := ⟨y,hy⟩) γ
  let η := chosenPath (⟨x,hx⟩ : U)
  let ζ : FlatPath U (base (⟨x,hx⟩ : U)).val y :=
    { chosenPath (⟨y,hy⟩ : U) with
      initial := fun t ht => (chosenPath (⟨y,hy⟩ : U)).initial t ht |>.trans
        (congrArg Subtype.val hb).symm }
  have h := path_independence hω hz (η.join γ) ζ
  rw [FlatPath.integral_join hω] at h
  change (chosenPath (⟨x,hx⟩ : U)).integral ω + γ.integral ω =
    (chosenPath (⟨y,hy⟩ : U)).integral ω at h
  simp only [potential, dite_eq_left hx, dite_eq_left hy]
  linarith

/-- The assembled component potentials have the prescribed Fréchet derivative
 at every point of the arbitrary open domain. -/
theorem potential_derivative {U : Set V} (ho : IsOpen U)
    {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) (hz : FlatClosedIntegralsVanish ω U)
    {x : V} (hx : x ∈ U) : HasFDerivAt (potential ω U) (ω x) x := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ho x hx
  have hxb : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  apply Exercise24.hasFDerivAt_of_segment_increment Metric.isOpen_ball (convex_ball x r)
    (hω.mono hsub) hxb
  intro y hy
  let γ := FlatPath.segment (convex_ball x r) hxb hy
  have h := potential_increment hω hz hx (hsub hy) (γ.mono hsub)
  change potential ω U y - potential ω U x = γ.integral ω at h
  rw [h]
  exact FlatPath.integral_segment (hω.mono hsub) (convex_ball x r) hxb hy

/-- C¹ regularity and exactness need only continuous coefficients. No
 connectedness assumption or nonempty-domain assumption is used. -/
theorem exactness_of_flat_closed {U : Set V} (ho : IsOpen U)
    {ω : SimplexIntegration.Form 1 V} (hω : ContinuousOn ω U)
    (hz : FlatClosedIntegralsVanish (PathIntegration.fromAlternating ω) U) :
    ContDiffOn ℝ 1 (potential (PathIntegration.fromAlternating ω) U) U ∧
      (∀ x ∈ U, HasFDerivAt (potential (PathIntegration.fromAlternating ω) U)
        (PathIntegration.fromAlternating ω x) x) ∧
      ∀ x ∈ U, extDeriv (PathIntegration.zeroForm
        (potential (PathIntegration.fromAlternating ω) U)) x = ω x := by
  have hc := Exercise24.fromAlternating_continuousOn hω
  have hd := fun x hx => potential_derivative ho hc hz (x := x) hx
  refine ⟨Exercise24.contDiffOn_of_hasFDerivAt ho hc hd, hd, ?_⟩
  intro x hx
  ext v
  have he := PathIntegration.exterior_potential (potential (PathIntegration.fromAlternating ω) U)
    x (v 0)
  rw [(hd x hx).fderiv] at he
  simpa only [PathIntegration.fromAlternating_apply,
    show (fun _ : Fin 1 => v 0) = v by ext i; fin_cases i; rfl] using he

/-- The source claim for every closed C¹ curve, on every open domain. -/
theorem exactness {U : Set V} (ho : IsOpen U)
    {ω : SimplexIntegration.Form 1 V} (hω : ContinuousOn ω U)
    (hz : ClosedIntegralsVanish (PathIntegration.fromAlternating ω) U) :
    ContDiffOn ℝ 1 (potential (PathIntegration.fromAlternating ω) U) U ∧
      (∀ x ∈ U, HasFDerivAt (potential (PathIntegration.fromAlternating ω) U)
        (PathIntegration.fromAlternating ω x) x) ∧
      ∀ x ∈ U, extDeriv (PathIntegration.zeroForm
        (potential (PathIntegration.fromAlternating ω) U)) x = ω x :=
  exactness_of_flat_closed ho hω hz.flat

/-- Every C¹ curve has its literal source Riemann integral. -/
theorem C1Curve.source {U : Set V} {ω : PathIntegration.OneForm V}
    (hω : ContinuousOn ω U) (γ : C1Curve U) :
    StieltjesPrototype.HasDarbouxRSIntegral (fun t => ω (γ.toFun t) (γ.velocity t)) id 0 1
      (γ.integral ω) := by
  have hc := (hω.comp γ.continuous γ.image).clm_apply γ.continuous_velocity
  have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (by norm_num : (0 : ℝ) ≤ 1) hc
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id, C1Curve.integral, Function.comp_def] using h

/-- The endpoint formula for all C¹ curves, including those with only one-sided
 endpoint derivatives. This also proves full C¹ path independence. -/
theorem curve_integral_of_flat_closed {U : Set V} (ho : IsOpen U)
    {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) (hz : FlatClosedIntegralsVanish ω U)
    (γ : C1Curve U) : γ.integral ω = potential ω U (γ.toFun 1) - potential ω U (γ.toFun 0) := by
  have hd := fun x hx => potential_derivative ho hω hz (x := x) hx
  have hc := Exercise24.contDiffOn_of_hasFDerivAt ho hω hd
  have hi := (hω.comp γ.continuous γ.image).clm_apply γ.continuous_velocity
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (hc.continuousOn.comp γ.continuous γ.image)
  · intro t ht
    exact (hd _ (γ.image ⟨ht.1.le, ht.2.le⟩)).comp_hasDerivAt t
      ((γ.derivative t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  · apply ContinuousOn.intervalIntegrable
    simpa using hi

/-- Endpoint formula under the original hypothesis on all closed C¹ curves. -/
theorem curve_integral {U : Set V} (ho : IsOpen U)
    {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) (hz : ClosedIntegralsVanish ω U)
    (γ : C1Curve U) : γ.integral ω = potential ω U (γ.toFun 1) - potential ω U (γ.toFun 0) :=
  curve_integral_of_flat_closed ho hω hz.flat γ

/-- Full path independence for arbitrary C¹ curves with common endpoints. -/
theorem c1_path_independence {U : Set V} (ho : IsOpen U)
    {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) (hz : ClosedIntegralsVanish ω U)
    (γ η : C1Curve U) (h0 : γ.toFun 0 = η.toFun 0) (h1 : γ.toFun 1 = η.toFun 1) :
    γ.integral ω = η.integral ω := by
  rw [curve_integral ho hω hz γ, curve_integral ho hω hz η, h0, h1]

/-- Reachability classes are open in the domain. -/
theorem reachable_isOpen {U : Set V} (ho : IsOpen U) (x : U) :
    IsOpen {y : U | Nonempty (FlatPath U x.val y.val)} := by
  rw [Metric.isOpen_iff]
  rintro y ⟨γ⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ho y.val y.property
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hzb : z.val ∈ Metric.ball y.val r := hz
  exact ⟨γ.join ((FlatPath.segment (convex_ball y.val r)
    (Metric.mem_ball_self hr) hzb).mono hsub)⟩

/-- The complement is also open; no connectedness of U is assumed. -/
theorem reachable_isClopen {U : Set V} (ho : IsOpen U) (x : U) :
    IsClopen {y : U | Nonempty (FlatPath U x.val y.val)} := by
  refine ⟨?_, reachable_isOpen ho x⟩
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro y hy
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ho y.val y.property
  refine ⟨r, hr, ?_⟩
  intro z hz ⟨γ⟩
  have hzb : z.val ∈ Metric.ball y.val r := hz
  exact hy ⟨γ.join (((FlatPath.segment (convex_ball y.val r)
    (Metric.mem_ball_self hr) hzb).mono hsub).reverse)⟩

/-- Every point of each topological component has one of the actual C¹ paths
 used in the construction. -/
theorem path_on_component {U : Set V} (ho : IsOpen U) (x y : U)
    (hy : y ∈ connectedComponent x) : Nonempty (FlatPath U x.val y.val) :=
  (reachable_isClopen ho x).connectedComponent_subset ⟨FlatPath.refl x.property⟩ hy

/-- The base point is constant on each topological component. -/
theorem base_eq_on_component {U : Set V} (ho : IsOpen U) (x y : U)
    (hy : y ∈ connectedComponent x) : base x = base y := by
  obtain ⟨γ⟩ := path_on_component ho x y hy
  exact base_eq γ

/-- Conversely each constructed path remains in its initial component. -/
theorem FlatPath.in_component {U : Set V} {x y : U} (γ : FlatPath U x.val y.val) :
    y ∈ connectedComponent x := by
  let p : ℝ → U := fun t => ⟨γ.toFun t, γ.image t⟩
  have hp : Continuous p := γ.smooth.continuous.subtype_mk _
  have h0 : p 0 = x := Subtype.ext γ.at_zero
  have h1 : p 1 = y := Subtype.ext γ.at_one
  exact (isPreconnected_range hp).subset_connectedComponent ⟨0,h0⟩ ⟨1,h1⟩

end Rudin.Chapter10.Exercise25
