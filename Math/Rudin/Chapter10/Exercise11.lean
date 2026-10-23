module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Compactness.SigmaCompact
public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Chapter10.Exercise01

/-! # Exercise 10.11: the strip-to-quadrant substitution -/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise11
open Set MeasureTheory
open scoped Real

/-- The source strip has neither its horizontal edges nor its left edge. -/
def strip : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo 0 1

def quadrant : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

def transform (p : ℝ × ℝ) : ℝ × ℝ := (p.1 - p.1 * p.2, p.1 * p.2)

def inverse (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + p.2, p.2 / (p.1 + p.2))

theorem mapsTo : MapsTo transform strip quadrant := by
  rintro ⟨s,t⟩ ⟨hs,ht⟩
  change 0 < s - s*t ∧ 0 < s*t
  exact ⟨by nlinarith [mul_pos hs (sub_pos.mpr ht.2)], mul_pos hs ht.1⟩

theorem inverse_mapsTo : MapsTo inverse quadrant strip := by
  rintro ⟨u,v⟩ ⟨hu,hv⟩
  change 0 < u at hu
  change 0 < v at hv
  change 0 < u+v ∧ 0 < v/(u+v) ∧ v/(u+v) < 1
  exact ⟨add_pos hu hv, div_pos hv (add_pos hu hv),
    (div_lt_one (add_pos hu hv)).mpr (by linarith)⟩

theorem left_inverse {p : ℝ × ℝ} (hp : p ∈ strip) : inverse (transform p) = p := by
  have hs : p.1 ≠ 0 := ne_of_gt hp.1
  ext <;> simp [inverse, transform, sub_add_cancel, hs]

theorem right_inverse {p : ℝ × ℝ} (hp : p ∈ quadrant) : transform (inverse p) = p := by
  have hs : p.1 + p.2 ≠ 0 := ne_of_gt (add_pos hp.1 hp.2)
  ext <;> dsimp [inverse, transform] <;> field_simp <;> ring

theorem bijection : BijOn transform strip quadrant :=
  ⟨mapsTo, fun p hp q hq h => by
    rw [← left_inverse hp, ← left_inverse hq, h],
    fun p hp => ⟨inverse p, inverse_mapsTo hp, right_inverse hp⟩⟩

/-- The derivative is an actual Fréchet derivative, not a formal matrix alone. -/
def derivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1-p.2, -p.1; p.2, p.1]).toContinuousLinearMap

theorem hasFDerivAt_transform (p : ℝ × ℝ) : HasFDerivAt transform (derivative p) p := by
  unfold derivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := p)
  have hg := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  convert! HasFDerivAt.prodMk (hf.sub (hf.mul hg)) (hf.mul hg) using 1
  ext q <;> simp [sub_smul] <;> ring

theorem jacobian (p : ℝ × ℝ) : (derivative p).det = p.1 := by
  simp [derivative, LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

/-- Change of variables for Bochner integrals on the full open strip. This
statement alone does not assert convergence of either integral. -/
theorem integral_transform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ℝ × ℝ) → E) :
    (∫ p in quadrant, f p) = ∫ p in strip, p.1 • f (transform p) := by
  rw [← bijection.image_eq]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun p _ => (hasFDerivAt_transform p).hasFDerivWithinAt) bijection.injOn]
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  simp only [jacobian, abs_of_pos hp.1]

/-- Absolute integrability is transported, not inferred from equality of the
possibly totalized Bochner integrals. -/
theorem integrable_transform_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ℝ × ℝ) → E) :
    IntegrableOn f quadrant ↔ IntegrableOn (fun p => p.1 • f (transform p)) strip := by
  rw [← bijection.image_eq]
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun p _ => (hasFDerivAt_transform p).hasFDerivWithinAt) bijection.injOn f
  rw [h]
  apply integrableOn_congr_fun _ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  simp only [jacobian, abs_of_pos hp.1]

/-- Euler's integrand, with its integrability supplied by the Gamma theorem. -/
def gammaKernel (x u : ℝ) : ℝ := Real.exp (-u) * u ^ (x-1)

def betaKernel (x y t : ℝ) : ℝ := t ^ (x-1) * (1-t) ^ (y-1)

def quadrantKernel (x y : ℝ) (p : ℝ × ℝ) : ℝ := gammaKernel y p.1 * gammaKernel x p.2

theorem kernel_transform (x y : ℝ) {p : ℝ × ℝ} (hp : p ∈ strip) :
    p.1 * quadrantKernel x y (transform p) =
      gammaKernel (x+y) p.1 * betaKernel x y p.2 := by
  have hs : 0 < p.1 := hp.1
  have ht : 0 < p.2 := hp.2.1
  have ht1 : 0 < 1-p.2 := sub_pos.mpr hp.2.2
  have hsub : p.1 - p.1*p.2 = p.1*(1-p.2) := by ring
  have hex : Real.exp (-(p.1-p.1*p.2)) * Real.exp (-(p.1*p.2)) =
      Real.exp (-p.1) := by rw [← Real.exp_add]; congr 1; ring
  have hpow : p.1 * (p.1 ^ (y-1) * p.1 ^ (x-1)) = p.1 ^ (x+y-1) := by
    calc
      _ = p.1 ^ (1:ℝ) * (p.1 ^ (y-1) * p.1 ^ (x-1)) := by rw [Real.rpow_one]
      _ = p.1 ^ (1 + ((y-1)+(x-1))) := by rw [Real.rpow_add hs, Real.rpow_add hs]
      _ = _ := by congr 1; ring
  dsimp [quadrantKernel, gammaKernel, betaKernel, transform]
  rw [hsub, Real.mul_rpow hs.le ht1.le, Real.mul_rpow hs.le ht.le]
  calc
    _ = (Real.exp (-(p.1*(1-p.2))) * Real.exp (-(p.1*p.2))) *
        (p.1 * (p.1 ^ (y-1) * p.1 ^ (x-1))) *
        (p.2 ^ (x-1) * (1-p.2) ^ (y-1)) := by ring
    _ = _ := by rw [← hsub,hex,hpow]

theorem quadrant_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (quadrantKernel x y) quadrant := by
  unfold IntegrableOn quadrant quadrantKernel gammaKernel
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (Real.GammaIntegral_convergent hy).mul_prod (Real.GammaIntegral_convergent hx)

theorem quadrant_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ p in quadrant, quadrantKernel x y p) = Real.Gamma x * Real.Gamma y := by
  unfold quadrantKernel quadrant
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (gammaKernel y) (gammaKernel x)]
  unfold gammaKernel
  rw [← Real.Gamma_eq_integral hy, ← Real.Gamma_eq_integral hx]
  ring

/-- The beta value is derived by the displayed two-dimensional substitution.
No beta-Gamma evaluation theorem is used. -/
theorem beta_gamma_Ioo {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in Ioo (0:ℝ) 1, betaKernel x y t) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x+y) := by
  have h := integral_transform (quadrantKernel x y)
  rw [quadrant_integral hx hy] at h
  have he : (∫ p in strip, p.1 • quadrantKernel x y (transform p)) =
      ∫ p in strip, gammaKernel (x+y) p.1 * betaKernel x y p.2 := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    exact kernel_transform x y hp
  rw [he, strip, Measure.volume_eq_prod, setIntegral_prod_mul] at h
  change Real.Gamma x * Real.Gamma y =
    (∫ s in Ioi 0, Real.exp (-s) * s ^ (x+y-1)) * _ at h
  rw [← Real.Gamma_eq_integral (add_pos hx hy)] at h
  apply (eq_div_iff (Real.Gamma_pos_of_pos (add_pos hx hy)).ne').mpr
  linarith

/-- A convergent exhaustion version of the substitution theorem. The
hypotheses on the exhaustion are stated separately from integrability. -/
theorem improper_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) → E} (hf : IntegrableOn f quadrant)
    (K : ℕ → Set (ℝ × ℝ)) (hK : ∀ n, IsCompact (K n))
    (hm : Monotone K) (hU : (⋃ n, K n) = strip) :
    (∀ n, (∫ p in transform '' K n, f p) = ∫ p in K n, p.1 • f (transform p)) ∧
    Filter.Tendsto (fun n => ∫ p in K n, p.1 • f (transform p)) Filter.atTop
      (nhds (∫ p in quadrant, f p)) ∧
    Filter.Tendsto (fun n => ∫ p in transform '' K n, f p) Filter.atTop
      (nhds (∫ p in quadrant, f p)) := by
  have hsub (n) : K n ⊆ strip := hU ▸ subset_iUnion K n
  have he (n) : (∫ p in transform '' K n, f p) = ∫ p in K n, p.1 • f (transform p) := by
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume (hK n).measurableSet
      (fun p _ => (hasFDerivAt_transform p).hasFDerivWithinAt)
      (bijection.injOn.mono (hsub n))]
    apply setIntegral_congr_fun (hK n).measurableSet
    intro p hp
    simp only [jacobian, abs_of_pos (hsub n hp).1]
  have hi := (integrable_transform_iff f).mp hf
  have ht := tendsto_setIntegral_of_monotone (fun n => (hK n).measurableSet) hm
    (hU.symm ▸ hi)
  rw [hU, ← integral_transform f] at ht
  exact ⟨he,ht,ht.congr (fun n => (he n).symm)⟩

theorem beta_gamma {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in (0:ℝ)..1, t ^ (x-1) * (1-t) ^ (y-1)) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x+y) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  exact beta_gamma_Ioo hx hy

/-- Integrability of the transformed kernel follows from the quadrant,
including both improper endpoints of the beta integral. -/
theorem strip_kernel_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun p : ℝ × ℝ => gammaKernel (x+y) p.1 * betaKernel x y p.2) strip := by
  have hi := (integrable_transform_iff (quadrantKernel x y)).mp (quadrant_integrable hx hy)
  exact hi.congr_fun (fun p hp => kernel_transform x y hp) (measurableSet_Ioi.prod measurableSet_Ioo)

/-- The beta integrand is absolutely integrable even when it is unbounded
near either endpoint. This is obtained from the transformed quadrant kernel. -/
theorem beta_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (betaKernel x y) (Ioo (0:ℝ) 1) := by
  have hi := strip_kernel_integrable hx hy
  unfold IntegrableOn strip at hi
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  have hj := hi.integral_prod_right
  have he : (fun t : ℝ => ∫ s in Ioi (0:ℝ),
      gammaKernel (x+y) s * betaKernel x y t) =
      (fun t => Real.Gamma (x+y) * betaKernel x y t) := by
    funext t
    rw [integral_mul_const]
    congr 1
    exact (Real.Gamma_eq_integral (add_pos hx hy)).symm
  rw [he] at hj
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (Real.Gamma_pos_of_pos (add_pos hx hy)).ne') _).mp hj

/-- The exhaustion hypotheses in `improper_extension` are realizable by
compact subsets of the open source strip. -/
theorem exists_strip_exhaustion : ∃ K : ℕ → Set (ℝ × ℝ),
    (∀ n, IsCompact (K n)) ∧ Monotone K ∧ (⋃ n, K n) = strip := by
  have ho : IsOpen strip := isOpen_Ioi.prod isOpen_Ioo
  letI : LocallyCompactSpace strip := ho.locallyCompactSpace
  let K : CompactExhaustion strip := default
  refine ⟨fun n => Subtype.val '' K n, fun n => (K.isCompact n).image continuous_subtype_val,
    fun i j hij => image_mono (K.subset hij), ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨i,q,hq,rfl⟩ := mem_iUnion.mp hp
    exact q.property
  · intro hp
    obtain ⟨n,hn⟩ := K.exists_mem ⟨p,hp⟩
    exact mem_iUnion.mpr ⟨n,⟨⟨p,hp⟩,hn,rfl⟩⟩

/-- On every compact interior interval the beta integrand has a literal
Darboux integral, including repeated partition nodes. -/
theorem beta_source_cut (x y : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (betaKernel x y) id a b
      (∫ t in a..b, betaKernel x y t) := by
  have hc : ContinuousOn (betaKernel x y) (Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    have ht1 : 1-t ≠ 0 := ne_of_gt (sub_pos.mpr (ht.2.trans_lt hb))
    exact ((continuousAt_id.rpow_const (Or.inl ht0)).mul
      ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl ht1))).continuousWithinAt
  have h := Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab hc
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id] using h

/-- Any increasing compact-interval exhaustion gives the source improper beta
value. Integrability and the value come from the quadrant substitution. -/
theorem beta_source_improper {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hb : ∀ n, b n < 1) (hm : Monotone (fun n => Icc (a n) (b n)))
    (hU : (⋃ n, Icc (a n) (b n)) = Ioo (0:ℝ) 1) :
    (∀ n, Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (betaKernel x y) id (a n) (b n)
      (∫ t in (a n)..(b n), betaKernel x y t)) ∧
    Filter.Tendsto (fun n => ∫ t in (a n)..(b n), betaKernel x y t) Filter.atTop
      (nhds (Real.Gamma x * Real.Gamma y / Real.Gamma (x+y))) := by
  refine ⟨fun n => beta_source_cut x y (ha n) (hab n) (hb n), ?_⟩
  have h := tendsto_setIntegral_of_monotone (fun n => measurableSet_Icc) hm
    (hU.symm ▸ beta_integrable hx hy)
  rw [hU, beta_gamma_Ioo hx hy] at h
  apply h.congr
  intro n
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hab n)]

/-- Closed interior rectangles. Reversed bounds give the empty set. -/
def cut (a b c d : ℝ) : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d

/-- The exact image is a closed convex trapezoid, possibly degenerate or empty. -/
def trapezoid (a b c d : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ b ∧
    c * (p.1 + p.2) ≤ p.2 ∧ p.2 ≤ d * (p.1 + p.2)}

theorem continuous_transform : Continuous transform := by
  unfold transform
  fun_prop

theorem cut_subset {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < 1) :
    cut a b c d ⊆ strip := by
  rintro p ⟨hs, ht⟩
  exact ⟨ha.trans_le hs.1, hc.trans_le ht.1, ht.2.trans_lt hd⟩

theorem image_cut {a b c d : ℝ} (ha : 0 < a) :
    transform '' cut a b c d = trapezoid a b c d := by
  ext p
  constructor
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
    change a ≤ s ∧ s ≤ b at hs
    change c ≤ t ∧ t ≤ d at ht
    have hpos : 0 < s := ha.trans_le hs.1
    dsimp [trapezoid, transform]
    have h1 := mul_le_mul_of_nonneg_left ht.1 hpos.le
    have h2 := mul_le_mul_of_nonneg_left ht.2 hpos.le
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> nlinarith
  · intro hp
    change a ≤ p.1+p.2 ∧ p.1+p.2 ≤ b ∧
      c*(p.1+p.2) ≤ p.2 ∧ p.2 ≤ d*(p.1+p.2) at hp
    have hpos : 0 < p.1+p.2 := ha.trans_le hp.1
    refine ⟨inverse p, ⟨⟨hp.1,hp.2.1⟩, ?_⟩, ?_⟩
    · exact ⟨(le_div_iff₀ hpos).mpr hp.2.2.1, (div_le_iff₀ hpos).mpr hp.2.2.2⟩
    · ext <;> dsimp [transform, inverse] <;> field_simp <;> ring

theorem convex_trapezoid (a b c d : ℝ) : Convex ℝ (trapezoid a b c d) := by
  intro p hp q hq r z hr hz hrz
  change a ≤ p.1+p.2 ∧ p.1+p.2 ≤ b ∧
    c*(p.1+p.2) ≤ p.2 ∧ p.2 ≤ d*(p.1+p.2) at hp
  change a ≤ q.1+q.2 ∧ q.1+q.2 ≤ b ∧
    c*(q.1+q.2) ≤ q.2 ∧ q.2 ≤ d*(q.1+q.2) at hq
  change a ≤ r*p.1+z*q.1+(r*p.2+z*q.2) ∧
    r*p.1+z*q.1+(r*p.2+z*q.2) ≤ b ∧
    c*(r*p.1+z*q.1+(r*p.2+z*q.2)) ≤ r*p.2+z*q.2 ∧
    r*p.2+z*q.2 ≤ d*(r*p.1+z*q.1+(r*p.2+z*q.2))
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hr (sub_nonneg.mpr hp.1), mul_nonneg hz (sub_nonneg.mpr hq.1),
      congrArg (fun w : ℝ => w*a) hrz]
  · nlinarith [mul_nonneg hr (sub_nonneg.mpr hp.2.1), mul_nonneg hz (sub_nonneg.mpr hq.2.1),
      congrArg (fun w : ℝ => w*b) hrz]
  · nlinarith [mul_nonneg hr (sub_nonneg.mpr hp.2.2.1), mul_nonneg hz (sub_nonneg.mpr hq.2.2.1)]
  · nlinarith [mul_nonneg hr (sub_nonneg.mpr hp.2.2.2), mul_nonneg hz (sub_nonneg.mpr hq.2.2.2)]

theorem compact_cut (a b c d : ℝ) : IsCompact (cut a b c d) :=
  isCompact_Icc.prod isCompact_Icc

theorem convex_cut (a b c d : ℝ) : Convex ℝ (cut a b c d) :=
  (convex_Icc a b).prod (convex_Icc c d)

theorem finite_cov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ℝ × ℝ) → E) {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < 1) :
    (∫ p in transform '' cut a b c d, f p) =
      ∫ p in cut a b c d, p.1 • f (transform p) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (compact_cut a b c d).measurableSet
    (fun p _ => (hasFDerivAt_transform p).hasFDerivWithinAt)
    (bijection.injOn.mono (cut_subset ha hc hd))]
  apply setIntegral_congr_fun (compact_cut a b c d).measurableSet
  intro p hp
  simp only [jacobian, abs_of_pos (cut_subset ha hc hd hp).1]

open Rudin.Chapter10.Exercise01

/-- Both sides have actual source integrals with the same value. The zero
extensions retain their closed boundary values. Every coordinate order and
all remaining parameters are included in the source predicates. -/
theorem finite_source_real {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < 1)
    {f : (ℝ × ℝ) → ℝ} (hf : ContinuousOn f (transform '' cut a b c d)) :
    HasPlaneSource (transform '' cut a b c d) f (∫ p in transform '' cut a b c d, f p) ∧
    HasPlaneSource (cut a b c d) (fun p => p.1 • f (transform p))
      (∫ p in transform '' cut a b c d, f p) := by
  refine ⟨plane_source_real ((compact_cut a b c d).image continuous_transform)
    (image_cut ha ▸ convex_trapezoid a b c d) hf, ?_⟩
  rw [finite_cov f ha hc hd]
  exact plane_source_real (compact_cut a b c d) (convex_cut a b c d)
    (continuous_fst.continuousOn.smul
      (hf.comp continuous_transform.continuousOn (mapsTo_image _ _)))

theorem finite_source_complex {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < 1)
    {f : (ℝ × ℝ) → ℂ} (hf : ContinuousOn f (transform '' cut a b c d)) :
    HasPlaneComplexSource (transform '' cut a b c d) f (∫ p in transform '' cut a b c d, f p) ∧
    HasPlaneComplexSource (cut a b c d) (fun p => p.1 • f (transform p))
      (∫ p in transform '' cut a b c d, f p) := by
  refine ⟨plane_source_complex ((compact_cut a b c d).image continuous_transform)
    (image_cut ha ▸ convex_trapezoid a b c d) hf, ?_⟩
  rw [finite_cov f ha hc hd]
  exact plane_source_complex (compact_cut a b c d) (convex_cut a b c d)
    (continuous_fst.continuousOn.smul
      (hf.comp continuous_transform.continuousOn (mapsTo_image _ _)))

/-- Explicit compact cutoffs stay strictly inside both improper endpoints. -/
def lower (j : ℕ) : ℝ := 1 / ((j : ℝ) + 3)
def upper (j : ℕ) : ℝ := (j : ℝ) + 3
def stripCut (j : ℕ) : Set (ℝ × ℝ) := cut (lower j) (upper j) (lower j) (1-lower j)

theorem lower_pos (j : ℕ) : 0 < lower j := by unfold lower; positivity

theorem lower_le_third (j : ℕ) : lower j ≤ 1/3 := by
  unfold lower
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3)
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem lower_antitone : Antitone lower := by
  intro i j hij
  apply one_div_le_one_div_of_le (by positivity : 0 < (i : ℝ)+3)
  have h : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  linarith

theorem stripCut_compact (j : ℕ) : IsCompact (stripCut j) := compact_cut _ _ _ _

theorem stripCut_subset (j : ℕ) : stripCut j ⊆ strip :=
  cut_subset (lower_pos j) (lower_pos j) (by linarith [lower_pos j])

theorem stripCut_monotone : Monotone stripCut := by
  intro i j hij p hp
  exact ⟨⟨(lower_antitone hij).trans hp.1.1,
    hp.1.2.trans (by dsimp [upper]; exact_mod_cast Nat.add_le_add_right hij 3)⟩,
    ⟨(lower_antitone hij).trans hp.2.1, hp.2.2.trans (by linarith [lower_antitone hij])⟩⟩

theorem stripCut_union : (⋃ j, stripCut j) = strip := by
  apply Subset.antisymm
  · exact iUnion_subset stripCut_subset
  · intro p hp
    have hs : 0 < p.1 := hp.1
    have ht : 0 < p.2 := hp.2.1
    have hu : 0 < 1-p.2 := sub_pos.mpr hp.2.2
    obtain ⟨j, hj⟩ := exists_nat_gt (max p.1 (max (1/p.1) (max (1/p.2) (1/(1-p.2)))))
    have hj1 : p.1 < (j : ℝ) := lt_of_le_of_lt (le_max_left _ _) hj
    have hj2 : 1/p.1 < (j : ℝ) := lt_of_le_of_lt
      ((le_max_left _ _).trans (le_max_right _ _)) hj
    have hj3 : 1/p.2 < (j : ℝ) := lt_of_le_of_lt
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hj
    have hj4 : 1/(1-p.2) < (j : ℝ) := lt_of_le_of_lt
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hj
    have hn : 0 < (j : ℝ)+3 := by positivity
    have hsmall (z : ℝ) (hz : 0 < z) (hjz : 1/z < (j : ℝ)) : lower j ≤ z := by
      apply (div_le_iff₀ hn).mpr
      have hh := (div_lt_iff₀ hz).mp hjz
      nlinarith
    exact mem_iUnion.mpr ⟨j, ⟨⟨hsmall _ hs hj2, by dsimp [upper]; linarith⟩,
      ⟨hsmall _ ht hj3, by linarith [hsmall _ hu hj4]⟩⟩⟩

theorem image_stripCut_union : (⋃ j, transform '' stripCut j) = quadrant := by
  rw [← image_iUnion, stripCut_union, bijection.image_eq]

theorem image_stripCut_compact (j : ℕ) : IsCompact (transform '' stripCut j) :=
  (stripCut_compact j).image continuous_transform

theorem image_stripCut_monotone : Monotone (fun j => transform '' stripCut j) :=
  fun _ _ h => image_mono (stripCut_monotone h)

theorem image_stripCut_convex (j : ℕ) : Convex ℝ (transform '' stripCut j) := by
  rw [stripCut, image_cut (lower_pos j)]
  exact convex_trapezoid _ _ _ _

/-- A limit of literal repeated source integrals. No measure integral occurs
in this definition. The exhaustion is specified by the caller. -/
def HasSourceLimit (H : ℕ → Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ) (v : ℝ) : Prop :=
  ∃ w : ℕ → ℝ, (∀ j, HasPlaneSource (H j) f (w j)) ∧
    Filter.Tendsto w Filter.atTop (nhds v)

def HasComplexSourceLimit (H : ℕ → Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℂ) (v : ℂ) : Prop :=
  ∃ w : ℕ → ℂ, (∀ j, HasPlaneComplexSource (H j) f (w j)) ∧
    Filter.Tendsto w Filter.atTop (nhds v)

/-- Source-to-source improper substitution under explicit sufficient conditions.
Only the original quadrant integrability is assumed. -/
theorem source_improper_real {f : (ℝ × ℝ) → ℝ}
    (hc : ContinuousOn f quadrant) (hi : IntegrableOn f quadrant) :
    IntegrableOn (fun p => p.1 • f (transform p)) strip ∧
    (∀ j, HasPlaneSource (transform '' stripCut j) f (∫ p in transform '' stripCut j, f p) ∧
      HasPlaneSource (stripCut j) (fun p => p.1 • f (transform p))
        (∫ p in transform '' stripCut j, f p)) ∧
    HasSourceLimit (fun j => transform '' stripCut j) f (∫ p in quadrant, f p) ∧
    HasSourceLimit stripCut (fun p => p.1 • f (transform p)) (∫ p in quadrant, f p) := by
  have hs (j) := finite_source_real (lower_pos j) (lower_pos j)
    (by linarith [lower_pos j] : 1-lower j < 1)
    (hc.mono (image_subset_iff.mpr (mapsTo.mono_left (stripCut_subset j))))
  have hl := (improper_extension hi stripCut stripCut_compact stripCut_monotone stripCut_union).2.2
  exact ⟨(integrable_transform_iff f).mp hi, hs,
    ⟨_, fun j => (hs j).1, hl⟩, ⟨_, fun j => (hs j).2, hl⟩⟩

theorem source_improper_complex {f : (ℝ × ℝ) → ℂ}
    (hc : ContinuousOn f quadrant) (hi : IntegrableOn f quadrant) :
    IntegrableOn (fun p => p.1 • f (transform p)) strip ∧
    (∀ j, HasPlaneComplexSource (transform '' stripCut j) f (∫ p in transform '' stripCut j, f p) ∧
      HasPlaneComplexSource (stripCut j) (fun p => p.1 • f (transform p))
        (∫ p in transform '' stripCut j, f p)) ∧
    HasComplexSourceLimit (fun j => transform '' stripCut j) f (∫ p in quadrant, f p) ∧
    HasComplexSourceLimit stripCut (fun p => p.1 • f (transform p)) (∫ p in quadrant, f p) := by
  have hs (j) := finite_source_complex (lower_pos j) (lower_pos j)
    (by linarith [lower_pos j] : 1-lower j < 1)
    (hc.mono (image_subset_iff.mpr (mapsTo.mono_left (stripCut_subset j))))
  have hl := (improper_extension hi stripCut stripCut_compact stripCut_monotone stripCut_union).2.2
  exact ⟨(integrable_transform_iff f).mp hi, hs,
    ⟨_, fun j => (hs j).1, hl⟩, ⟨_, fun j => (hs j).2, hl⟩⟩

theorem gamma_continuous (x : ℝ) : ContinuousOn (gammaKernel x) (Ioi 0) := by
  intro u hu
  exact ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
    (continuousAt_id.rpow_const (Or.inl (ne_of_gt hu)))).continuousWithinAt

theorem quadrant_continuous (x y : ℝ) : ContinuousOn (quadrantKernel x y) quadrant :=
  ((gamma_continuous y).comp continuous_fst.continuousOn (fun _ hp => hp.1)).mul
    ((gamma_continuous x).comp continuous_snd.continuousOn (fun _ hp => hp.2))

theorem gamma_source_cut (x : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (gammaKernel x) id a b
      (∫ s in a..b, gammaKernel x s) := by
  have h := Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab
    ((gamma_continuous x).mono (fun _ hu => ha.trans_le hu.1))
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id] using h

theorem lower_le_upper (j : ℕ) : lower j ≤ upper j := by
  have h := lower_le_third j
  dsimp [upper]
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem beta_cut_order (j : ℕ) : lower j ≤ 1-lower j := by
  linarith [lower_le_third j]

theorem gamma_cut_monotone : Monotone (fun j => Icc (lower j) (upper j)) := by
  intro i j hij s hs
  exact ⟨(lower_antitone hij).trans hs.1,
    hs.2.trans (by dsimp [upper]; exact_mod_cast Nat.add_le_add_right hij 3)⟩

theorem beta_cut_monotone : Monotone (fun j => Icc (lower j) (1-lower j)) := by
  intro i j hij t ht
  exact ⟨(lower_antitone hij).trans ht.1, ht.2.trans (by linarith [lower_antitone hij])⟩

theorem gamma_cut_union : (⋃ j, Icc (lower j) (upper j)) = Ioi (0:ℝ) := by
  ext s
  constructor
  · intro hs
    obtain ⟨j,hj⟩ := mem_iUnion.mp hs
    exact (lower_pos j).trans_le hj.1
  · intro hs
    have hp : (s,(1/2:ℝ)) ∈ ⋃ j, stripCut j := by
      rw [stripCut_union]
      exact ⟨hs, by norm_num, by norm_num⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨j,hj.1⟩

theorem beta_cut_union : (⋃ j, Icc (lower j) (1-lower j)) = Ioo (0:ℝ) 1 := by
  ext t
  constructor
  · intro ht
    obtain ⟨j,hj⟩ := mem_iUnion.mp ht
    exact ⟨(lower_pos j).trans_le hj.1, by linarith [hj.2, lower_pos j]⟩
  · intro ht
    have hp : ((1:ℝ),t) ∈ ⋃ j, stripCut j := by
      rw [stripCut_union]
      exact ⟨by norm_num, ht⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨j,hj.2⟩

theorem gamma_cut_limit {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun j => ∫ s in (lower j)..(upper j), gammaKernel x s)
      Filter.atTop (nhds (Real.Gamma x)) := by
  have h := tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) gamma_cut_monotone
    (gamma_cut_union.symm ▸ Real.GammaIntegral_convergent hx)
  rw [gamma_cut_union, ← Real.Gamma_eq_integral hx] at h
  apply h.congr
  intro j
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (lower_le_upper j)]
  rfl

/-- Euler's Gamma integral as a limit of actual finite Darboux integrals. -/
theorem gamma_source_improper {x : ℝ} (hx : 0 < x) :
    (∀ j, Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (gammaKernel x) id
      (lower j) (upper j) (∫ s in (lower j)..(upper j), gammaKernel x s)) ∧
    Filter.Tendsto (fun j => ∫ s in (lower j)..(upper j), gammaKernel x s)
      Filter.atTop (nhds (Real.Gamma x)) :=
  ⟨fun j => gamma_source_cut x (lower_pos j) (lower_le_upper j), gamma_cut_limit hx⟩

/-- This limit needs only the derived integrability, not the beta evaluation. -/
theorem beta_cut_limit_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Filter.Tendsto (fun j => ∫ t in (lower j)..(1-lower j), betaKernel x y t)
      Filter.atTop (nhds (∫ t in Ioo (0:ℝ) 1, betaKernel x y t)) := by
  have h := tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) beta_cut_monotone
    (beta_cut_union.symm ▸ beta_integrable hx hy)
  rw [beta_cut_union] at h
  apply h.congr
  intro j
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (beta_cut_order j)]

/-- Finite COV followed by product Fubini on the actual rectangle. The product
on the right consists of genuine one-dimensional source cutoff values. -/
theorem kernel_finite_cov (x y : ℝ) (j : ℕ) :
    (∫ p in transform '' stripCut j, quadrantKernel x y p) =
      (∫ s in (lower j)..(upper j), gammaKernel (x+y) s) *
      (∫ t in (lower j)..(1-lower j), betaKernel x y t) := by
  rw [show (∫ p in transform '' stripCut j, quadrantKernel x y p) =
    ∫ p in stripCut j, p.1 • quadrantKernel x y (transform p) from
    finite_cov (quadrantKernel x y) (lower_pos j) (lower_pos j)
      (by linarith [lower_pos j])]
  have he : (∫ p in stripCut j, p.1 • quadrantKernel x y (transform p)) =
      ∫ p in stripCut j, gammaKernel (x+y) p.1 * betaKernel x y p.2 := by
    apply setIntegral_congr_fun (stripCut_compact j).measurableSet
    intro p hp
    exact kernel_transform x y (stripCut_subset j hp)
  rw [he, stripCut, cut, Measure.volume_eq_prod, setIntegral_prod_mul]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (lower_le_upper j),
    ← intervalIntegral.integral_of_le (beta_cut_order j)]

/-- Source witnesses on both sides of the finite two-dimensional substitution,
with the factorized finite value, not just two measure-integral names. -/
theorem kernel_finite_source (x y : ℝ) (j : ℕ) :
    let v := (∫ s in (lower j)..(upper j), gammaKernel (x+y) s) *
      (∫ t in (lower j)..(1-lower j), betaKernel x y t)
    HasPlaneSource (transform '' stripCut j) (quadrantKernel x y) v ∧
    HasPlaneSource (stripCut j) (fun p => p.1 • quadrantKernel x y (transform p)) v := by
  dsimp only
  rw [← kernel_finite_cov]
  exact finite_source_real (lower_pos j) (lower_pos j) (by linarith [lower_pos j])
    ((quadrant_continuous x y).mono
      (image_subset_iff.mpr (mapsTo.mono_left (stripCut_subset j))))

/-- The common finite source values converge to the quadrant Gamma product.
This is the finite source COV limit used in the beta evaluation. -/
theorem kernel_source_product_limit {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∀ j, let v := (∫ s in (lower j)..(upper j), gammaKernel (x+y) s) *
        (∫ t in (lower j)..(1-lower j), betaKernel x y t)
      HasPlaneSource (transform '' stripCut j) (quadrantKernel x y) v ∧
      HasPlaneSource (stripCut j) (fun p => p.1 • quadrantKernel x y (transform p)) v) ∧
    Filter.Tendsto (fun j =>
      (∫ s in (lower j)..(upper j), gammaKernel (x+y) s) *
      (∫ t in (lower j)..(1-lower j), betaKernel x y t))
      Filter.atTop (nhds (Real.Gamma x * Real.Gamma y)) := by
  refine ⟨kernel_finite_source x y, ?_⟩
  have hq := (improper_extension (quadrant_integrable hx hy) stripCut stripCut_compact
    stripCut_monotone stripCut_union).2.2
  rw [quadrant_integral hx hy] at hq
  exact hq.congr (kernel_finite_cov x y)

/-- Derivation of (96) by limits of the finite source COV and finite Fubini
identities. This proof does not use either previous beta evaluation theorem. -/
theorem beta_gamma_from_source_cuts {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in Ioo (0:ℝ) 1, betaKernel x y t) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x+y) := by
  have hq := (kernel_source_product_limit hx hy).2
  have hp := (gamma_cut_limit (add_pos hx hy)).mul (beta_cut_limit_integral hx hy)
  have hv' := tendsto_nhds_unique hq hp
  apply (eq_div_iff (Real.Gamma_pos_of_pos (add_pos hx hy)).ne').mpr
  nlinarith [hv']

/-- Complete source limit package, including the one-dimensional Gamma and
beta cutoffs and both two-dimensional source integrals. -/
theorem beta_source_derivation {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∀ j, Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (gammaKernel (x+y)) id
      (lower j) (upper j) (∫ s in (lower j)..(upper j), gammaKernel (x+y) s) ∧
      Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (betaKernel x y) id
        (lower j) (1-lower j) (∫ t in (lower j)..(1-lower j), betaKernel x y t)) ∧
    HasSourceLimit (fun j => transform '' stripCut j) (quadrantKernel x y)
      (Real.Gamma x * Real.Gamma y) ∧
    HasSourceLimit stripCut (fun p => p.1 • quadrantKernel x y (transform p))
      (Real.Gamma x * Real.Gamma y) ∧
    Filter.Tendsto (fun j => ∫ t in (lower j)..(1-lower j), betaKernel x y t)
      Filter.atTop (nhds (Real.Gamma x * Real.Gamma y / Real.Gamma (x+y))) := by
  have hs := (source_improper_real (quadrant_continuous x y) (quadrant_integrable hx hy)).2.2
  rw [quadrant_integral hx hy] at hs
  refine ⟨fun j => ⟨gamma_source_cut _ (lower_pos j) (lower_le_upper j),
    beta_source_cut _ _ (lower_pos j) (beta_cut_order j) (by linarith [lower_pos j])⟩,
    hs.1, hs.2, ?_⟩
  rw [← beta_gamma_from_source_cuts hx hy]
  exact beta_cut_limit_integral hx hy

/-- The quadrant integrand in the printed exercise, in its printed order.
The earlier kernel uses the exchanged parameters so that t has exponent x-1. -/
def printedKernel (x y : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 ^ (x-1) * Real.exp (-p.1) * p.2 ^ (y-1) * Real.exp (-p.2)

theorem printedKernel_eq (x y : ℝ) : printedKernel x y = quadrantKernel y x := by
  funext p
  dsimp [printedKernel, quadrantKernel, gammaKernel]
  ring

/-- In the printed parameter order, the substitution gives beta(y,x).
Exchanging the arbitrary positive parameters gives exactly (96). -/
theorem printed_source_derivation {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (printedKernel x y) quadrant ∧
    HasSourceLimit (fun j => transform '' stripCut j) (printedKernel x y)
      (Real.Gamma x * Real.Gamma y) ∧
    HasSourceLimit stripCut (fun p => p.1 • printedKernel x y (transform p))
      (Real.Gamma x * Real.Gamma y) ∧
    (∀ j, let v := (∫ s in (lower j)..(upper j), gammaKernel (x+y) s) *
        (∫ t in (lower j)..(1-lower j), betaKernel y x t)
      HasPlaneSource (transform '' stripCut j) (printedKernel x y) v ∧
      HasPlaneSource (stripCut j) (fun p => p.1 • printedKernel x y (transform p)) v) := by
  rw [printedKernel_eq]
  have hs := beta_source_derivation hy hx
  simpa only [add_comm y x, mul_comm (Real.Gamma y) (Real.Gamma x)] using
    (show IntegrableOn (quadrantKernel y x) quadrant ∧
      HasSourceLimit (fun j => transform '' stripCut j) (quadrantKernel y x)
        (Real.Gamma y * Real.Gamma x) ∧
      HasSourceLimit stripCut (fun p => p.1 • quadrantKernel y x (transform p))
        (Real.Gamma y * Real.Gamma x) ∧
      (∀ j, let v := (∫ s in (lower j)..(upper j), gammaKernel (y+x) s) *
          (∫ t in (lower j)..(1-lower j), betaKernel y x t)
        HasPlaneSource (transform '' stripCut j) (quadrantKernel y x) v ∧
        HasPlaneSource (stripCut j) (fun p => p.1 • quadrantKernel y x (transform p)) v)
      from ⟨quadrant_integrable hy hx, hs.2.1, hs.2.2.1, kernel_finite_source y x⟩)

/-- Finite continuity proves integrability on both domains, independently of
any convention for the value of a nonintegrable measure integral. -/
theorem finite_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c d : ℝ} {f : (ℝ × ℝ) → E}
    (hf : ContinuousOn f (transform '' cut a b c d)) :
    IntegrableOn f (transform '' cut a b c d) ∧
    IntegrableOn (fun p => p.1 • f (transform p)) (cut a b c d) :=
  ⟨hf.integrableOn_compact ((compact_cut a b c d).image continuous_transform),
    (continuous_fst.continuousOn.smul
      (hf.comp continuous_transform.continuousOn (mapsTo_image _ _))).integrableOn_compact
        (compact_cut a b c d)⟩

theorem reversed_cut_first {a b c d : ℝ} (h : b < a) : cut a b c d = ∅ := by
  simp [cut, Icc_eq_empty_of_lt h]

theorem reversed_cut_second {a b c d : ℝ} (h : d < c) : cut a b c d = ∅ := by
  simp [cut, Icc_eq_empty_of_lt h]

/-- The positive-exponent condition cannot be relaxed at the left endpoint. -/
theorem beta_left_threshold (x : ℝ) :
    IntegrableOn (betaKernel x 1) (Ioo (0:ℝ) 1) ↔ 0 < x := by
  change IntegrableOn (fun t : ℝ => t ^ (x-1) * (1-t) ^ ((1:ℝ)-1)) (Ioo 0 1) ↔ _
  simp only [sub_self, Real.rpow_zero, mul_one]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- Reflection gives the same sharp condition at the right endpoint. -/
theorem beta_right_threshold (y : ℝ) :
    IntegrableOn (betaKernel 1 y) (Ioo (0:ℝ) 1) ↔ 0 < y := by
  rw [← beta_left_threshold y]
  change IntegrableOn (fun t : ℝ => t ^ ((1:ℝ)-1) * (1-t) ^ (y-1)) (Ioo 0 1) ↔
    IntegrableOn (fun t : ℝ => t ^ (y-1) * (1-t) ^ ((1:ℝ)-1)) (Ioo 0 1)
  simp only [sub_self, Real.rpow_zero, one_mul, mul_one]
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (zero_le_one : (0:ℝ) ≤ 1),
    ← intervalIntegrable_iff_integrableOn_Ioo_of_le (zero_le_one : (0:ℝ) ≤ 1)]
  rw [IntervalIntegrable.symm_iff (a := (0:ℝ)) (b := 1)]
  simpa only [sub_zero, sub_self] using
    (IntervalIntegrable.comp_sub_left_iff (f := fun t : ℝ => t ^ (y-1)) (a := 0) (b := 1) 1)

end Rudin.Chapter10.Exercise11
