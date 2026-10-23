module

public import Math.Rudin.Chapter10.Exercise09
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Exercise 10.10: decay and convergence of expanding regions

The norm is Euclidean. Finite disk, rectangle, and polar cuts have literal
source values. Their improper and absolute limits use the stated decay bound.
-/
@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise10
open Set MeasureTheory Filter
open scoped Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The selected sufficient decay condition. It applies to real and complex
coefficients, and retains the case `C=0`. -/
def Decay {E : Type*} [NormedAddCommGroup E] (f : Plane → E) : Prop :=
  Continuous f ∧ ∃ C q : ℝ, 0 ≤ C ∧ 2 < q ∧
    ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-q)

/-- Disk-cutoff definition of the improper integral. -/
def HasDiskIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (v : E) : Prop :=
  Tendsto (fun R : ℝ => ∫ x in Metric.closedBall (0 : Plane) R, f x) atTop (𝓝 v)

/-- Coordinate rectangles, with the original Cartesian axes. -/
def rectangle (R : ℝ) : Set Plane := {x | ∀ i, |x i| ≤ R}

def HasRectangleIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (v : E) : Prop :=
  Tendsto (fun R : ℝ => ∫ x in rectangle R, f x) atTop (𝓝 v)

theorem integrable_of_decay {E : Type*} [NormedAddCommGroup E] {f : Plane → E}
    (hf : Decay f) : Integrable f := by
  obtain ⟨hc,C,q,hC,hq,hbound⟩ := hf
  have hi : Integrable (fun x : Plane => (1 + ‖x‖) ^ (-q)) :=
    integrable_one_add_norm (by simpa using hq)
  exact (hi.const_mul C).mono' hc.aestronglyMeasurable (Eventually.of_forall hbound)

theorem disk_exhaustion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Integrable f) : HasDiskIntegral f (∫ x, f x) := by
  have hu : (⋃ R : ℝ, Metric.closedBall (0 : Plane) R) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨‖x‖, by simp⟩
  have h := tendsto_setIntegral_of_monotone
    (fun R : ℝ => measurableSet_closedBall (x := (0 : Plane)) (ε := R))
    (fun i j hij => Metric.closedBall_subset_closedBall hij)
    (hf.integrableOn (s := ⋃ R : ℝ, Metric.closedBall (0 : Plane) R))
  simpa [hu, HasDiskIntegral] using h

theorem rectangle_measurable (R : ℝ) : MeasurableSet (rectangle R) := by
  have : rectangle R = ⋂ i : Fin 2, {x : Plane | |x i| ≤ R} := by ext; simp [rectangle]
  rw [this]
  exact MeasurableSet.iInter fun i => isClosed_le (by fun_prop) continuous_const |>.measurableSet

theorem rectangle_exhaustion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Integrable f) : HasRectangleIntegral f (∫ x, f x) := by
  have hu : (⋃ R : ℝ, rectangle R) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    refine ⟨max |x 0| |x 1|, ?_⟩
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hm : Monotone rectangle := fun i j hij x hx k => (hx k).trans hij
  have h := tendsto_setIntegral_of_monotone rectangle_measurable hm
    (hf.integrableOn (s := ⋃ R : ℝ, rectangle R))
  simpa [hu, HasRectangleIntegral] using h

/-- Absolute convergence and agreement of the disk and rectangle cutoffs. -/
theorem decay_convergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Decay f) :
    Integrable f ∧ Integrable (fun x => ‖f x‖) ∧
    HasDiskIntegral f (∫ x, f x) ∧ HasRectangleIntegral f (∫ x, f x) ∧
    HasDiskIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) ∧
    HasRectangleIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) := by
  have hi := integrable_of_decay hf
  exact ⟨hi,hi.norm,disk_exhaustion hi,rectangle_exhaustion hi,
    disk_exhaustion hi.norm,rectangle_exhaustion hi.norm⟩

open Rudin.Support.MultivariateRiemann
open scoped Real

/-- Cartesian polar coordinates interpreted in the Euclidean plane. -/
def polar (r θ : ℝ) : Plane := pairCoordinates.symm (Exercise09.transform (r,θ))

theorem norm_coordinates (p : ℝ × ℝ) :
    ‖pairCoordinates.symm p‖ = Real.sqrt (p.1^2+p.2^2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, pairCoordinates, Real.norm_eq_abs, sq_abs]

theorem disk_preimage {a : ℝ} (ha : 0 ≤ a) :
    pairCoordinates.symm ⁻¹' Metric.closedBall (0:Plane) a = Exercise09.disk a := by
  ext p
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_coordinates]
  exact Real.sqrt_le_left ha

theorem disk_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x in Metric.closedBall (0:Plane) a, f x) =
      ∫ r in (0:ℝ)..a, ∫ θ in (0:ℝ)..(2*π), r • f (polar r θ) := by
  have h := pairCoordinates_symm_volume.setIntegral_preimage_emb
    pairCoordinates.symm.toHomeomorph.measurableEmbedding f (Metric.closedBall (0:Plane) a)
  rw [disk_preimage ha] at h
  rw [← h]
  exact Exercise09.polar_integral_by_approximation ha (hf.comp pairCoordinates.symm.continuous).continuousOn

/-- The radial improper integral keeps the full angular interval at every cutoff. -/
def HasPolarIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) (v : E) : Prop :=
  Tendsto (fun a : ℝ => ∫ r in (0:ℝ)..a, ∫ θ in (0:ℝ)..(2*π), r • f (polar r θ))
    atTop (𝓝 v)

/-- Passage to the limit uses the finite-disk identity, not a reassignment of
angular and radial bounds. -/
theorem whole_plane_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Decay f) : HasPolarIntegral f (∫ x, f x) := by
  have ht := disk_exhaustion (integrable_of_decay hf)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
  exact disk_polar hf.1 ha

/-- Absolute convergence of the radial cutoff, for real or complex functions. -/
theorem absolute_polar_convergence {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} (hf : Decay f) : HasPolarIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) := by
  have ht := disk_exhaustion (integrable_of_decay hf).norm
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
  exact disk_polar hf.1.norm ha

/-- The Gaussian used in the source, with the Euclidean norm. -/
def gaussian (x : Plane) : ℝ := Real.exp (-‖x‖^2)

theorem gaussian_decay : Decay gaussian := by
  refine ⟨by unfold gaussian; fun_prop, 24, 4, by norm_num, by norm_num, ?_⟩
  intro x
  have h₁ := Real.pow_div_factorial_le_exp (‖x‖^2) (sq_nonneg _) 2
  have h₂ := add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (norm_nonneg x) 4
  have h₃ := Real.one_le_exp_iff.mpr (sq_nonneg ‖x‖)
  norm_num at h₁ h₂
  have hp : (1+‖x‖)^4 ≤ 24 * Real.exp (‖x‖^2) := by nlinarith
  have hd : 0 < (1+‖x‖)^4 := by positivity
  dsimp only [gaussian]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖x‖), Real.rpow_ofNat, Real.exp_neg]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hd).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (Real.exp_pos (‖x‖^2))).mpr hp

theorem gaussian_polar (r θ : ℝ) : gaussian (polar r θ) = Real.exp (-r^2) := by
  unfold gaussian polar
  rw [norm_coordinates, Exercise09.sum_sq, Real.sq_sqrt (sq_nonneg r)]

theorem radial_gaussian_integral (a : ℝ) :
    (∫ r in (0:ℝ)..a, r * Real.exp (-r^2)) = (1 - Real.exp (-a^2))/2 := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => -(Real.exp (-r^2))/2)
      (r * Real.exp (-r^2)) r := by
    convert! ((((hasDerivAt_id r).pow 2).neg.exp).neg.div_const 2) using 1 <;>
      simp [Pi.neg_apply, Pi.pow_apply, id_eq] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp
  ring

theorem gaussian_cutoff (a : ℝ) :
    (∫ r in (0:ℝ)..a, ∫ θ in (0:ℝ)..(2*π), r • gaussian (polar r θ)) =
      π * (1 - Real.exp (-a^2)) := by
  simp only [gaussian_polar, smul_eq_mul, intervalIntegral.integral_const, sub_zero]
  rw [intervalIntegral.integral_const_mul, radial_gaussian_integral]
  ring

/-- The plane value follows by letting the radius tend to infinity in the
proved polar formula, after checking the fixed decay condition. -/
theorem gaussian_plane_integral : (∫ x, gaussian x) = π := by
  have hp := whole_plane_polar gaussian_decay
  have he : Tendsto (fun a : ℝ => Real.exp (-a^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)))
  have hv : Tendsto (fun a : ℝ => π * (1 - Real.exp (-a^2))) atTop (𝓝 π) := by
    simpa using (tendsto_const_nhds (x := π)).mul ((tendsto_const_nhds (x := (1:ℝ))).sub he)
  have hp' : Tendsto (fun a : ℝ => π * (1 - Real.exp (-a^2))) atTop
      (𝓝 (∫ x, gaussian x)) := by
    simpa only [HasPolarIntegral, gaussian_cutoff] using hp
  exact tendsto_nhds_unique hp' hv

/-- Fubini now derives, rather than assumes, the one-dimensional value. -/
theorem gaussian_integral : Integrable (fun s : ℝ => Real.exp (-s^2)) ∧
    (∫ s : ℝ, Real.exp (-s^2)) = Real.sqrt π := by
  refine ⟨by simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1), ?_⟩
  have hc := pairCoordinates_symm_volume.integral_comp
    pairCoordinates.symm.toHomeomorph.measurableEmbedding gaussian
  have he : (fun p : ℝ × ℝ => gaussian (pairCoordinates.symm p)) =
      (fun p => Real.exp (-p.1^2) * Real.exp (-p.2^2)) := by
    funext p
    rw [gaussian, norm_coordinates, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      ← Real.exp_add]
    congr 1
    ring
  rw [he, gaussian_plane_integral, Measure.volume_eq_prod,
    integral_prod_mul (fun s : ℝ => Real.exp (-s^2)) (fun s : ℝ => Real.exp (-s^2))] at hc
  have hn : 0 ≤ ∫ s : ℝ, Real.exp (-s^2) := integral_nonneg (fun s => (Real.exp_pos _).le)
  have hs := Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.sqrt_nonneg π]

/-- Under the literal differential/bound assignment, θ is the variable whose
upper limit tends to infinity. This is not a radial exhaustion. -/
def literalCutoff (A : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..A, ∫ r in (0:ℝ)..(2*π), r * gaussian (polar r θ)

theorem literal_cutoff_value (A : ℝ) :
    literalCutoff A = A * ((1 - Real.exp (-(2*π)^2))/2) := by
  simp only [literalCutoff, gaussian_polar, radial_gaussian_integral,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]

theorem literal_order_obstruction :
    Tendsto literalCutoff atTop atTop := by
  have hp : 0 < (1 - Real.exp (-(2*π)^2))/2 := by
    apply div_pos _ (by norm_num)
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, sq_pos_of_pos Real.pi_pos]
  have h := tendsto_id.atTop_mul_const hp
  exact h.congr (fun A => (literal_cutoff_value A).symm)

/-- Every finite Gaussian cut has the literal source Darboux value. -/
theorem gaussian_finite_source {a b : ℝ} (hab : a ≤ b) :
    Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral
      (fun s : ℝ => Real.exp (-s^2)) id a b
      (∫ s in a..b, Real.exp (-s^2)) := by
  have h := Rudin.Support.StieltjesMeasureBridge.continuous_bridge
    StieltjesFunction.id hab (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp (-s^2)) (Icc a b))
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id] using h

/-- The Gaussian value is the limit of the literal finite cuts, not merely a
value of the totalized whole-line integral. -/
theorem gaussian_improper :
    Tendsto (fun R : ℝ => ∫ s in (-R)..R, Real.exp (-s^2)) atTop (𝓝 (Real.sqrt π)) := by
  have h := intervalIntegral_tendsto_integral gaussian_integral.1
    tendsto_neg_atTop_atBot tendsto_id
  simpa only [gaussian_integral.2, id_eq] using h

/-- In particular, the literal printed binding cannot equal the finite plane
integral π proved above. -/
theorem literal_no_finite_value (v : ℝ) : ¬ Tendsto literalCutoff atTop (𝓝 v) :=
  not_tendsto_nhds_of_tendsto_atTop literal_order_obstruction v

open Exercise01

/-- Literal Euclidean zero-extension source integrals in every Cartesian order. -/
def HasFiniteRealSource (H : Set Plane) (f : Plane → ℝ) (v : ℝ) : Prop :=
  ∃ a b : Fin 2 → ℝ, (∀ i, a i < b i) ∧
    H ⊆ (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b ∧
    IntegrableOn f H ∧ ∀ σ : Equiv.Perm (Fin 2),
    HasSourceIntegral 2 (a ∘ σ) (b ∘ σ)
      (H.indicator f ∘ (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ coordinatePermutation σ) v

def HasFiniteComplexSource (H : Set Plane) (f : Plane → ℂ) (v : ℂ) : Prop :=
  ∃ a b : Fin 2 → ℝ, (∀ i, a i < b i) ∧
    H ⊆ (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b ∧
    IntegrableOn f H ∧ ∀ σ : Equiv.Perm (Fin 2),
    HasComplexSourceIntegral 2 (a ∘ σ) (b ∘ σ)
      (H.indicator f ∘ (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ coordinatePermutation σ) v

/-- These are compact convex Euclidean coordinate rectangles, not disks for
the product norm. The assertion also covers the empty negative cutoffs. -/
theorem rectangle_compact_convex (R : ℝ) : IsCompact (rectangle R) ∧ Convex ℝ (rectangle R) := by
  have he : rectangle R = (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹'
      Icc (fun _ => -R) (fun _ => R) := by
    ext x
    simp only [rectangle, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def,
      EuclideanSpace.equiv]
    simp only [abs_le, forall_and]
    rfl
  rw [he]
  exact ⟨(EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc,
    (convex_Icc _ _).affine_preimage (EuclideanSpace.equiv (Fin 2) ℝ).toAffineEquiv.toAffineMap⟩

/-- Finite source witnesses are established before any improper limit. -/
theorem finite_source_real {f : Plane → ℝ} (hf : Continuous f) {R : ℝ} (hR : 0 ≤ R) :
    HasFiniteRealSource (Metric.closedBall (0:Plane) R) f
      (∫ x in Metric.closedBall (0:Plane) R, f x) ∧
    HasFiniteRealSource (rectangle R) f (∫ x in rectangle R, f x) ∧
    HasSourceIntegral 2 ![0,0] ![2*π,R]
      (fun u => u 1 * f (polar (u 1) (u 0)))
      (∫ x in Metric.closedBall (0:Plane) R, f x) := by
  refine ⟨existence_real (isCompact_closedBall _ _) (convex_closedBall _ _) hf.continuousOn,
    existence_real (rectangle_compact_convex R).1 (rectangle_compact_convex R).2 hf.continuousOn, ?_⟩
  have h := Exercise09.polar_source_real hR (hf.comp pairCoordinates.symm.continuous).continuousOn
  have he := pairCoordinates_symm_volume.setIntegral_preimage_emb
    pairCoordinates.symm.toHomeomorph.measurableEmbedding f (Metric.closedBall (0:Plane) R)
  rw [disk_preimage hR] at he
  simpa only [Function.comp_apply, he, polar] using h

theorem finite_source_complex {f : Plane → ℂ} (hf : Continuous f) {R : ℝ} (hR : 0 ≤ R) :
    HasFiniteComplexSource (Metric.closedBall (0:Plane) R) f
      (∫ x in Metric.closedBall (0:Plane) R, f x) ∧
    HasFiniteComplexSource (rectangle R) f (∫ x in rectangle R, f x) ∧
    HasComplexSourceIntegral 2 ![0,0] ![2*π,R]
      (fun u => u 1 • f (polar (u 1) (u 0)))
      (∫ x in Metric.closedBall (0:Plane) R, f x) := by
  refine ⟨existence_complex (isCompact_closedBall _ _) (convex_closedBall _ _) hf.continuousOn,
    existence_complex (rectangle_compact_convex R).1 (rectangle_compact_convex R).2 hf.continuousOn, ?_⟩
  have h := Exercise09.polar_source_complex_tagged hR (hf.comp pairCoordinates.symm.continuous).continuousOn
  have he := pairCoordinates_symm_volume.setIntegral_preimage_emb
    pairCoordinates.symm.toHomeomorph.measurableEmbedding f (Metric.closedBall (0:Plane) R)
  rw [disk_preimage hR] at he
  simpa only [Function.comp_apply, he, polar] using h

/-- All finite real source values, their absolute counterparts, and their
improper limits under exactly `Decay`, including a zero bound. -/
theorem whole_plane_source_real {f : Plane → ℝ} (hf : Decay f) :
    (∀ R : ℝ, 0 ≤ R →
      HasFiniteRealSource (Metric.closedBall (0:Plane) R) f
        (∫ x in Metric.closedBall (0:Plane) R, f x) ∧
      HasFiniteRealSource (rectangle R) f (∫ x in rectangle R, f x) ∧
      HasSourceIntegral 2 ![0,0] ![2*π,R]
        (fun u => u 1 * f (polar (u 1) (u 0))) (∫ x in Metric.closedBall (0:Plane) R, f x)) ∧
    (∀ R : ℝ, 0 ≤ R →
      HasFiniteRealSource (Metric.closedBall (0:Plane) R) (fun x => ‖f x‖)
        (∫ x in Metric.closedBall (0:Plane) R, ‖f x‖) ∧
      HasFiniteRealSource (rectangle R) (fun x => ‖f x‖) (∫ x in rectangle R, ‖f x‖) ∧
      HasSourceIntegral 2 ![0,0] ![2*π,R]
        (fun u => u 1 * ‖f (polar (u 1) (u 0))‖) (∫ x in Metric.closedBall (0:Plane) R, ‖f x‖)) ∧
    Integrable f ∧ Integrable (fun x => ‖f x‖) ∧
    HasDiskIntegral f (∫ x, f x) ∧ HasRectangleIntegral f (∫ x, f x) ∧
    HasDiskIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) ∧
    HasRectangleIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) ∧
    HasPolarIntegral f (∫ x, f x) ∧ HasPolarIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) := by
  obtain ⟨hi,hn,hd,hr,hdn,hrn⟩ := decay_convergence hf
  exact ⟨fun _ hR => finite_source_real hf.1 hR,
    fun _ hR => finite_source_real hf.1.norm hR, hi,hn,hd,hr,hdn,hrn,
    whole_plane_polar hf, absolute_polar_convergence hf⟩

/-- Complex source convergence uses actual complex tagged finite cuts. -/
theorem whole_plane_source_complex {f : Plane → ℂ} (hf : Decay f) :
    (∀ R : ℝ, 0 ≤ R →
      HasFiniteComplexSource (Metric.closedBall (0:Plane) R) f
        (∫ x in Metric.closedBall (0:Plane) R, f x) ∧
      HasFiniteComplexSource (rectangle R) f (∫ x in rectangle R, f x) ∧
      HasComplexSourceIntegral 2 ![0,0] ![2*π,R]
        (fun u => u 1 • f (polar (u 1) (u 0))) (∫ x in Metric.closedBall (0:Plane) R, f x)) ∧
    (∀ R : ℝ, 0 ≤ R →
      HasFiniteRealSource (Metric.closedBall (0:Plane) R) (fun x => ‖f x‖)
        (∫ x in Metric.closedBall (0:Plane) R, ‖f x‖) ∧
      HasFiniteRealSource (rectangle R) (fun x => ‖f x‖) (∫ x in rectangle R, ‖f x‖) ∧
      HasSourceIntegral 2 ![0,0] ![2*π,R]
        (fun u => u 1 * ‖f (polar (u 1) (u 0))‖) (∫ x in Metric.closedBall (0:Plane) R, ‖f x‖)) ∧
    Integrable f ∧ Integrable (fun x => ‖f x‖) ∧
    HasDiskIntegral f (∫ x, f x) ∧ HasRectangleIntegral f (∫ x, f x) ∧
    HasDiskIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) ∧
    HasRectangleIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) ∧
    HasPolarIntegral f (∫ x, f x) ∧ HasPolarIntegral (fun x => ‖f x‖) (∫ x, ‖f x‖) := by
  obtain ⟨hi,hn,hd,hr,hdn,hrn⟩ := decay_convergence hf
  exact ⟨fun _ hR => finite_source_complex hf.1 hR,
    fun _ hR => finite_source_real hf.1.norm hR, hi,hn,hd,hr,hdn,hrn,
    whole_plane_polar hf, absolute_polar_convergence hf⟩

end Rudin.Chapter10.Exercise10
