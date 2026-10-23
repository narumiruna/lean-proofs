module

public import Math.Rudin.Support.MultivariateRiemann
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Compactness.SigmaCompact

/-! # Exercise 10.9: polar geometry with the positive-x-axis seam -/
@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise09
open Set MeasureTheory Filter
open scoped Real

/-- These are Cartesian coordinates, not the product norm's closed ball. -/
def disk (a : ℝ) : Set (ℝ × ℝ) := {p | p.1^2 + p.2^2 ≤ a^2}

def rectangle (a : ℝ) : Set (ℝ × ℝ) := Icc 0 a ×ˢ Icc 0 (2*π)

def transform (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)

theorem sum_sq (p : ℝ × ℝ) : (transform p).1^2 + (transform p).2^2 = p.1^2 := by
  dsimp [transform]
  nlinarith [Real.cos_sq_add_sin_sq p.2]

theorem mapsTo (a : ℝ) : MapsTo transform (rectangle a) (disk a) := by
  intro p hp
  change (transform p).1^2 + (transform p).2^2 ≤ a^2
  rw [sum_sq]
  exact pow_le_pow_left₀ hp.1.1 hp.1.2 _

/-- The zero-radius rectangle is allowed. -/
theorem range (a : ℝ) (ha : 0 ≤ a) : transform '' rectangle a = disk a := by
  apply subset_antisymm (image_subset_iff.mpr (mapsTo a))
  rintro ⟨x,y⟩ hp
  let z : ℂ := ⟨x,y⟩
  let θ := if 0 ≤ z.arg then z.arg else z.arg + 2*π
  have hr : ‖z‖ ≤ a := by
    rw [Complex.norm_def]
    apply (Real.sqrt_le_left ha).mpr
    simpa [Complex.normSq_apply, z, disk, sq] using hp
  have ht : θ ∈ Icc (0 : ℝ) (2*π) := by
    dsimp [θ]
    split_ifs with h
    · exact ⟨h, (Complex.arg_le_pi z).trans (by linarith [Real.pi_pos])⟩
    · constructor
      · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
      · linarith
  have hc : Real.cos θ = Real.cos z.arg := by
    dsimp [θ]; split_ifs <;> simp
  have hs : Real.sin θ = Real.sin z.arg := by
    dsimp [θ]; split_ifs <;> simp
  refine ⟨(‖z‖,θ), ⟨⟨norm_nonneg _,hr⟩,ht⟩, ?_⟩
  ext
  · change ‖z‖ * Real.cos θ = x
    rw [hc, Complex.norm_mul_cos_arg]
  · change ‖z‖ * Real.sin θ = y
    rw [hs, Complex.norm_mul_sin_arg]

/-- Shift by π and negate the target to use the standard negative-axis chart. -/
theorem shifted (p : ℝ × ℝ) :
    polarCoord.symm (p.1,p.2-π) = - transform p := by
  ext <;> simp [polarCoord, transform, Real.cos_sub, Real.sin_sub]

/-- No seam identification occurs inside the printed angular interval. -/
theorem interior_injective (a : ℝ) :
    InjOn transform (Ioo 0 a ×ˢ Ioo 0 (2*π)) := by
  intro p hp q hq h
  have hp' : (p.1,p.2-π) ∈ polarCoord.target :=
    ⟨hp.1.1, by constructor <;> linarith [hp.2.1,hp.2.2]⟩
  have hq' : (q.1,q.2-π) ∈ polarCoord.target :=
    ⟨hq.1.1, by constructor <;> linarith [hq.2.1,hq.2.2]⟩
  have he := polarCoord.symm.injOn hp' hq' (by rw [shifted,shifted,h])
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  ext <;> dsimp at h₁ h₂ <;> linarith

theorem hasFDerivAt_transform (p : ℝ × ℝ) :
    HasFDerivAt transform (fderivPolarCoordSymm p) p :=
  hasFDerivAt_polarCoord_symm p

theorem jacobian (p : ℝ × ℝ) : (fderivPolarCoordSymm p).det = p.1 :=
  det_fderivPolarCoordSymm p

/-- Literal printed bounds with the usual nested differential binding, for
`f=1` and `a=1`. The radial variable has the incorrect bound `2π`. -/
theorem literal_value : (∫ θ in (0:ℝ)..1, ∫ r in (0:ℝ)..(2*π), r) = 2*π^2 := by
  simp [integral_id]
  ring

/-- The corrected bound assignment has value π for the same constant function. -/
theorem corrected_constant_value :
    (∫ r in (0:ℝ)..1, ∫ θ in (0:ℝ)..(2*π), r) = π := by
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

theorem literal_order_obstruction :
    (∫ θ in (0:ℝ)..1, ∫ r in (0:ℝ)..(2*π), r) ≠
      (∫ r in (0:ℝ)..1, ∫ θ in (0:ℝ)..(2*π), r) := by
  rw [literal_value, corrected_constant_value]
  nlinarith [Real.pi_gt_three]

/-- Positive radial coordinate and the full angular interval with its seam removed. -/
def slitRectangle (a : ℝ) : Set (ℝ × ℝ) := Ioc 0 a ×ˢ Ioo 0 (2*π)

/-- The omitted radius is on the positive x-axis, not the positive y-axis. -/
def slitDisk (a : ℝ) : Set (ℝ × ℝ) := disk a ∩ {p | -p ∈ polarCoord.source}

theorem slit_injective (a : ℝ) : InjOn transform (slitRectangle a) := by
  apply (interior_injective (a+1)).mono
  intro p hp
  exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩,hp.2⟩

theorem image_slit (a : ℝ) (ha : 0 ≤ a) :
    transform '' slitRectangle a = slitDisk a := by
  apply subset_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    refine ⟨mapsTo a ⟨⟨hp.1.1.le,hp.1.2⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩, ?_⟩
    change -transform p ∈ polarCoord.source
    rw [← shifted]
    apply polarCoord.map_target
    exact ⟨hp.1.1, by constructor <;> linarith [hp.2.1,hp.2.2]⟩
  · intro p hp
    have ht := polarCoord.map_source hp.2
    let q := polarCoord (-p)
    have hr : q.1 ≤ a := by
      change Real.sqrt ((-p).1^2 + (-p).2^2) ≤ a
      apply (Real.sqrt_le_left ha).mpr
      simpa [disk] using hp.1
    refine ⟨(q.1,q.2+π), ⟨⟨ht.1,hr⟩, ?_⟩, ?_⟩
    · change 0 < q.2+π ∧ q.2+π < 2*π
      constructor <;> linarith [ht.2.1,ht.2.2]
    · have he := polarCoord.left_inv hp.2
      have hh := shifted (q.1,q.2+π)
      simp only [add_sub_cancel_right] at hh
      change polarCoord.symm q = -p at he
      rw [he] at hh
      exact neg_injective hh.symm

theorem slit_ae_disk (a : ℝ) : slitDisk a =ᵐ[volume] disk a := by
  have hn : volume ((univ : Set ℝ) ×ˢ ({0}:Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hh : ∀ᵐ p : ℝ × ℝ ∂volume, p ∉ (univ : Set ℝ) ×ˢ {0} := by
    rw [ae_iff]
    convert hn using 2
    ext p
    simp
  filter_upwards [hh] with p hp
  have hy : p.2 ≠ 0 := by simpa using hp
  have hs : -p ∈ polarCoord.source := by right; simpa using hy
  apply propext
  change (p ∈ disk a ∧ -p ∈ polarCoord.source) ↔ p ∈ disk a
  exact and_iff_left hs

/-- The measure change of variables has no compact-interior-support hypothesis.
A separate source-Riemann comparison is still required. -/
theorem disk_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) (f : (ℝ × ℝ) → E) :
    (∫ p in disk a, f p) = ∫ p in slitRectangle a, p.1 • f (transform p) := by
  rw [← setIntegral_congr_set (slit_ae_disk a), ← image_slit a ha,
    integral_image_eq_integral_abs_det_fderiv_smul volume
      (measurableSet_Ioc.prod measurableSet_Ioo)
      (fun p _ => (hasFDerivAt_transform p).hasFDerivWithinAt) (slit_injective a)]
  apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
  intro p hp
  simp only [jacobian, abs_of_pos hp.1.1]

theorem disk_isCompact (a : ℝ) (ha : 0 ≤ a) : IsCompact (disk a) := by
  rw [← range a ha]
  apply (isCompact_Icc.prod isCompact_Icc).image
  exact continuous_iff_continuousAt.mpr (fun p => (hasFDerivAt_transform p).continuousAt)

theorem polar_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 ≤ a) {f : (ℝ × ℝ) → E} (hf : ContinuousOn f (disk a)) :
    IntegrableOn f (disk a) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 • f (transform p)) (slitRectangle a) := by
  have hi : IntegrableOn f (disk a) := hf.integrableOn_compact (disk_isCompact a ha)
  refine ⟨hi, ?_⟩
  have hc : ContinuousOn (fun p : ℝ × ℝ => p.1 • f (transform p)) (rectangle a) :=
    continuous_fst.continuousOn.smul (hf.comp
      (continuous_iff_continuousAt.mpr (fun p => (hasFDerivAt_transform p).continuousAt)).continuousOn
      (mapsTo a))
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (fun p hp => ⟨⟨hp.1.1.le,hp.1.2⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩)

/-- Explicit radial and angular binding; valid also for complex coefficients
and radius zero. This is the Bochner formulation. -/
theorem polar_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 ≤ a) {f : (ℝ × ℝ) → E} (hf : ContinuousOn f (disk a)) :
    (∫ p in disk a, f p) = ∫ r in (0:ℝ)..a, ∫ θ in (0:ℝ)..(2*π),
      r • f (transform (r,θ)) := by
  rw [disk_integral a ha, slitRectangle, Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by
    have hi := (polar_integrable ha hf).2
    unfold slitRectangle at hi
    rw [Measure.volume_eq_prod] at hi
    exact hi)]
  rw [intervalIntegral.integral_of_le ha]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  dsimp only
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*π), integral_Ioc_eq_integral_Ioo]

theorem disk_area_one : (∫ p in disk 1, (1:ℝ)) = π := by
  rw [polar_integral (by norm_num : (0:ℝ) ≤ 1) continuousOn_const]
  simpa using corrected_constant_value

theorem literal_disk_obstruction :
    (∫ θ in (0:ℝ)..1, ∫ r in (0:ℝ)..(2*π), r) ≠ (∫ p in disk 1, (1:ℝ)) := by
  rw [literal_value, disk_area_one]
  nlinarith [Real.pi_gt_three]

/-- The disk is convex for the Euclidean norm, not the product sup norm. -/
theorem disk_convex (a : ℝ) (ha : 0 ≤ a) : Convex ℝ (disk a) := by
  let e := Rudin.Support.MultivariateRiemann.pairCoordinates.symm
  have he : e ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) a = disk a := by
    ext p
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hn : ‖e p‖ = Real.sqrt (p.1^2+p.2^2) := by
      simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two,
        Rudin.Support.MultivariateRiemann.pairCoordinates, Real.norm_eq_abs, sq_abs]
    rw [hn]
    exact Real.sqrt_le_left ha
  rw [← he]
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) a).linear_preimage e.toLinearMap

/-- The open domain for the stated angular branch. -/
def openSlit (a : ℝ) : Set (ℝ × ℝ) := interior (disk a) ∩ {p | -p ∈ polarCoord.source}

theorem openSlit_isOpen (a : ℝ) : IsOpen (openSlit a) :=
  isOpen_interior.inter (polarCoord.open_source.preimage continuous_neg)

theorem openSlit_ae_disk (a : ℝ) (ha : 0 ≤ a) : openSlit a =ᵐ[volume] disk a := by
  have hi := interior_ae_eq_of_null_frontier ((disk_convex a ha).addHaar_frontier volume)
  have hs := slit_ae_disk a
  filter_upwards [hi,hs] with p hp hq
  change ((p ∈ interior (disk a)) ∧ -p ∈ polarCoord.source) = (p ∈ disk a)
  rw [hp]
  exact hq

/-- Continuous compact-interior cutoffs remove the support restriction. The
omitted circle and positive-x-axis radius are included in the null-set proof.
The coefficient can be real or complex, and need only be continuous on the disk. -/
theorem slit_approximation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 ≤ a) {f : (ℝ × ℝ) → E} (hf : ContinuousOn f (disk a)) :
    ∃ χ : ℕ → C(ℝ × ℝ, ℝ),
      (∀ n, IsCompact (tsupport (χ n)) ∧ tsupport (χ n) ⊆ openSlit a ∧
        ∀ p, χ n p ∈ Icc (0:ℝ) 1) ∧
      (∀ n, Continuous (fun p => χ n p • f p)) ∧
      (∀ p ∈ openSlit a, Filter.Tendsto (fun n => χ n p) Filter.atTop (nhds 1)) ∧
      Filter.Tendsto (fun n => ∫ p in disk a, χ n p • f p) Filter.atTop
        (nhds (∫ p in disk a, f p)) := by
  have ho := openSlit_isOpen a
  letI : LocallyCompactSpace (openSlit a) := ho.locallyCompactSpace
  let K : CompactExhaustion (openSlit a) := default
  have hK (n) : IsCompact (Subtype.val '' K n : Set (ℝ × ℝ)) :=
    (K.isCompact n).image continuous_subtype_val
  have hsub (n) : (Subtype.val '' K n : Set (ℝ × ℝ)) ⊆ openSlit a := by
    rintro _ ⟨p,_,rfl⟩
    exact p.property
  choose χ he hk hs hb using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) ho (hsub n)
  have hc (n) : Continuous (fun p => χ n p • f p) := by
    apply continuous_of_tsupport
    intro p hp
    have hi : p ∈ interior (disk a) := (hs n (tsupport_smul_subset_left _ _ hp)).1
    exact (χ n).continuous.continuousAt.smul (hf.continuousAt (mem_interior_iff_mem_nhds.mp hi))
  have ht (p) (hp : p ∈ openSlit a) :
      Filter.Tendsto (fun n => χ n p) Filter.atTop (nhds 1) := by
    obtain ⟨n,hn⟩ := K.exists_mem ⟨p,hp⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (he m ⟨⟨p,hp⟩,K.subset hm hn,rfl⟩).symm
  refine ⟨χ, fun n => ⟨hk n,hs n,hb n⟩,hc,ht, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun p => ‖f p‖)
    (fun n => (hc n).aestronglyMeasurable)
    ((polar_integrable ha hf).1.norm)
  · intro n
    apply Filter.Eventually.of_forall
    intro p
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb n p).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb n p).2
  · have hh := ae_restrict_of_ae (s := disk a) (openSlit_ae_disk a ha)
    filter_upwards [hh, ae_restrict_mem (disk_isCompact a ha).measurableSet] with p hp hd
    have hu : p ∈ openSlit a := hp.mpr hd
    simpa using (ht p hu).smul (tendsto_const_nhds (x := f p))

open Rudin.Support.MultivariateRiemann

/-- The corrected polar side consists of literal repeated Darboux integrals.
Coordinate zero is θ; coordinate one is r, so θ is integrated first. -/
theorem polar_source_real {a : ℝ} (ha : 0 ≤ a) {f : (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f (disk a)) :
    HasSourceIntegral 2 ![0,0] ![2*π,a]
      (fun u => u 1 * f (transform (u 1,u 0))) (∫ p in disk a, f p) := by
  have hab : (![0,0] : Fin 2 → ℝ) ≤ ![2*π,a] := by
    intro i
    fin_cases i <;> simp [ha, Real.pi_pos.le]
  have hc : ContinuousOn (fun u : Fin 2 → ℝ => u 1 * f (transform (u 1,u 0)))
      (Icc ![0,0] ![2*π,a]) := by
    apply (continuous_apply 1).continuousOn.mul
    apply hf.comp
    · exact (continuous_iff_continuousAt.mpr
        (fun p => (hasFDerivAt_transform p).continuousAt)).continuousOn.comp (by fun_prop)
        (fun _ _ => mem_univ _)
    · intro u hu
      apply mapsTo a
      exact ⟨⟨hu.1 1,hu.2 1⟩,⟨hu.1 0,hu.2 0⟩⟩
  have h := source_of_continuousOn hab hc
  rw [polar_integral ha hf]
  simpa [iterated, smul_eq_mul] using h

/-- Literal source witnesses for both components of a complex coefficient.
The real/imaginary decomposition uses the actual complex integral value. -/
theorem polar_source_complex {a : ℝ} (ha : 0 ≤ a) {f : (ℝ × ℝ) → ℂ}
    (hf : ContinuousOn f (disk a)) :
    HasSourceIntegral 2 ![0,0] ![2*π,a]
      (fun u => u 1 * (f (transform (u 1,u 0))).re) (∫ p in disk a, f p).re ∧
    HasSourceIntegral 2 ![0,0] ![2*π,a]
      (fun u => u 1 * (f (transform (u 1,u 0))).im) (∫ p in disk a, f p).im := by
  have hi := (polar_integrable ha hf).1
  constructor
  · have h := polar_source_real ha (Complex.continuous_re.comp_continuousOn hf)
    have hr : (∫ p in disk a, (f p).re) = (∫ p in disk a, f p).re := integral_re hi
    simpa only [Function.comp_apply, hr] using h
  · have h := polar_source_real ha (Complex.continuous_im.comp_continuousOn hf)
    have hr : (∫ p in disk a, (f p).im) = (∫ p in disk a, f p).im := integral_im hi
    simpa only [Function.comp_apply, hr] using h

end Rudin.Chapter10.Exercise09
