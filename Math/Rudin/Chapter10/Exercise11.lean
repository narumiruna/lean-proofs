module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Compactness.SigmaCompact
public import Math.Rudin.Support.RiemannIntegrability

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

end Rudin.Chapter10.Exercise11
