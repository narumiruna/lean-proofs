module

public import Math.Rudin.Support.TriangleStokes
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Convex.Measure

/-!
# Coordinate and source integral comparison

Volume normalization uses the actual Euclidean coordinate map. Source integrals
use the existing one-dimensional Darboux predicate, not a renamed measure integral.
For real coefficients continuous on compact boxes or closed standard simplexes,
every repeated source integral exists and all coordinate orders have the same
value. The zero extension retains boundary values. Its first marginal is proved
continuous by a variable-endpoint integral, and Fubini then gives the comparison.
The pinned BoxIntegral Riemann integral has the same value. The standard simplex
has Euclidean volume `1/n!`, including dimension zero.

The two-dimensional comparison also transports the actual derivative and basis
in `simplexIntegral` to `formIntegral`. General form coefficients inherit the
source comparison from their proved continuity. No orientation quotient,
reparameterization, arbitrary image-volume formula, or Stokes theorem is asserted.

Sources: Rudin 10.1–10.4, 10.26, and the slice integral in the proof of 10.33
(PDF pages 254–257, 275, 282–284). Remarks 10.35 require further chain and Stokes
results; no conclusion there or Chapter 10 exercise is certified by this file.
-/

@[expose] public section
noncomputable section
namespace Rudin.Support.MultivariateRiemann

open Set MeasureTheory SimplexIntegration

/-- A real coefficient continuous on a closed set has an ambient continuous
extension. No values outside the set are prescribed. -/
theorem continuous_extension {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) {f : X → ℝ} (hf : ContinuousOn f s) :
    ∃ g : X → ℝ, Continuous g ∧ EqOn g f s := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hs
    (⟨fun x : s => f x, hf.domRestrict⟩ : C(s, ℝ))
  refine ⟨g, g.continuous, ?_⟩
  intro x hx
  exact congrArg (fun h : C(s, ℝ) => h ⟨x, hx⟩) hg

/-- Euclidean volume and product-coordinate volume have the same normalization,
including dimension zero. This is not an isometry claim for the sup norm. -/
theorem coordinates_volume (n : ℕ) :
    MeasurePreserving (EuclideanSpace.equiv (Fin n) ℝ) volume volume :=
  PiLp.volume_preserving_ofLp (Fin n)

/-- The inverse coordinates also preserve volume. -/
theorem coordinates_symm_volume (n : ℕ) :
    MeasurePreserving (EuclideanSpace.equiv (Fin n) ℝ).symm volume volume :=
  PiLp.volume_preserving_toLp (Fin n)

/-- The pair chart has the ordered coordinates `(u₀,u₁)`. -/
def pairCoordinates : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem pairCoordinates_volume : MeasurePreserving pairCoordinates volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (coordinates_volume 2)

theorem pairCoordinates_symm_volume :
    MeasurePreserving pairCoordinates.symm volume volume := by
  exact pairCoordinates_volume.symm pairCoordinates.toHomeomorph.toMeasurableEquiv

@[simp] theorem pairCoordinates_simplex :
    pairCoordinates ⁻¹' triangle = standardSimplex 2 := by
  ext u
  simp [pairCoordinates, triangle, standardSimplex, Fin.forall_fin_two,
    Fin.sum_univ_two, and_assoc]

@[simp] theorem pairCoordinates_symm_triangle :
    pairCoordinates.symm ⁻¹' standardSimplex 2 = triangle := by
  ext p
  change pairCoordinates.symm p ∈ standardSimplex 2 ↔ p ∈ triangle
  rw [← pairCoordinates_simplex]
  simp only [mem_preimage, pairCoordinates.apply_symm_apply]

/-- Values on the closed triangle determine its variable-bound integral. -/
theorem triangleIntegral_congr {f g : (ℝ × ℝ) → ℝ} (h : EqOn f g triangle) :
    triangleIntegral f = triangleIntegral g := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc (0 : ℝ) (1 - x) := by
    simpa [uIcc_of_le (sub_nonneg.mpr hx'.2)] using hy
  exact h (show (x,y) ∈ triangle from ⟨hx'.1, hy'.1, by linarith [hy'.2]⟩)

/-- Fubini for the literal zero extension proves the triangle comparison. -/
theorem triangle_setIntegral_of_continuous (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    (∫ p in triangle, f p) = triangleIntegral f := by
  have hsub : triangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩,
      ⟨hp.2.1, by linarith [hp.1, hp.2.2]⟩⟩
  calc
    _ = ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, triangleZeroExtension f p := by
      rw [triangleZeroExtension, setIntegral_indicator triangle_isClosed.measurableSet,
        inter_eq_right.mpr hsub]
    _ = ∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1,
        triangleZeroExtension f (x,y) := by
      exact setIntegral_prod _ (by
        simpa only [← Measure.volume_eq_prod] using triangleZeroExtension_integrable f hf)
    _ = ∫ x in 0..1, ∫ y in 0..1, triangleZeroExtension f (x,y) := by
      simp_rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    _ = triangleIntegral f := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact triangleZeroExtension_integral f (by simpa using hx)

/-- Only continuity on the compact triangle is required. -/
theorem triangle_setIntegral (f : (ℝ × ℝ) → ℝ) (hf : ContinuousOn f triangle) :
    (∫ p in triangle, f p) = triangleIntegral f := by
  obtain ⟨g, hg, he⟩ := continuous_extension triangle_isClosed hf
  rw [← setIntegral_congr_fun triangle_isClosed.measurableSet he,
    triangle_setIntegral_of_continuous g hg, triangleIntegral_congr he]

/-- The Euclidean simplex integral equals the pair-coordinate iterated integral.
Its coefficient is integrable by compactness and continuity. -/
theorem euclidean_triangle_integral (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ContinuousOn f (standardSimplex 2)) :
    IntegrableOn f (standardSimplex 2) ∧
      (∫ u in standardSimplex 2, f u) = triangleIntegral (f ∘ pairCoordinates.symm) := by
  refine ⟨hf.integrableOn_compact (standardSimplex_isCompact 2), ?_⟩
  have h := pairCoordinates_symm_volume.setIntegral_preimage_emb
    pairCoordinates.symm.toHomeomorph.measurableEmbedding f (standardSimplex 2)
  rw [pairCoordinates_symm_triangle] at h
  rw [← h]
  apply triangle_setIntegral
  exact hf.comp pairCoordinates.symm.continuous.continuousOn
    (fun p hp => show p ∈ pairCoordinates.symm ⁻¹' standardSimplex 2 from
      pairCoordinates_symm_triangle ▸ hp)

/-- The closed-domain source convention also needs no ambient continuity. -/
theorem triangle_source (f : (ℝ × ℝ) → ℝ) (hf : ContinuousOn f triangle) :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => triangleZeroExtension f (x,y)) id 0 1
      (∫ y in 0..(1-x), f (x,y))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..1, triangleZeroExtension f (x,y)) id 0 1
      (triangleIntegral f) := by
  obtain ⟨g, hg, he⟩ := continuous_extension triangle_isClosed hf
  have hz : triangleZeroExtension g = triangleZeroExtension f :=
    indicator_congr he
  have hv : triangleIntegral g = triangleIntegral f := triangleIntegral_congr he
  obtain ⟨hi, ho⟩ := triangle_source_riemann g hg
  constructor
  · intro x hx
    rw [hz] at hi
    convert hi x hx using 1
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) (1-x) := by
      simpa [uIcc_of_le (sub_nonneg.mpr hx.2)] using hy
    exact (he (show (x,y) ∈ triangle from
      ⟨hx.1, hy'.1, by linarith [hy'.2]⟩)).symm
  · rwa [hz, hv] at ho

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transport of actual derivatives and the ordered basis on the parameter
triangle. The coefficient identity is proved, not assumed. -/
theorem simplexCoefficient_pair (ω : Form 2 E) (S : SmoothSimplex 2 E)
    {p : ℝ × ℝ} (hp : p ∈ triangle) :
    simplexCoefficient ω S (pairCoordinates.symm p) =
      triangleCoefficient ω (S.toFun ∘ pairCoordinates.symm) p := by
  have hu : pairCoordinates.symm p ∈ standardSimplex 2 :=
    show p ∈ pairCoordinates.symm ⁻¹' standardSimplex 2 from
      pairCoordinates_symm_triangle ▸ hp
  rw [simplexCoefficient, triangleCoefficient, pullback_apply, pullback_apply,
    fderiv_comp p (S.differentiableAt hu) pairCoordinates.symm.differentiableAt]
  congr 1
  funext i
  simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  congr 1
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [pairCoordinates, EuclideanSpace.single]

/-- This closes the existing Euclidean `simplexIntegral` / pair `formIntegral`
gap for all continuous forms on a smooth parameter triangle. -/
theorem simplexIntegral_eq_formIntegral (ω : Form 2 E) (S : SmoothSimplex 2 E)
    (hω : ContinuousOn ω (S.toFun '' standardSimplex 2)) :
    simplexIntegral ω S = formIntegral ω (S.toFun ∘ pairCoordinates.symm) := by
  exact (euclidean_triangle_integral _ (simplexCoefficient_continuousOn ω S hω)).2.trans
    (triangleIntegral_congr (fun p hp => simplexCoefficient_pair ω S hp))

/-- Pair-coordinate pullback regularity follows from simplex-only regularity. -/
theorem triangleCoefficient_continuousOn (ω : Form 2 E) (S : SmoothSimplex 2 E)
    (hω : ContinuousOn ω (S.toFun '' standardSimplex 2)) :
    ContinuousOn (triangleCoefficient ω (S.toFun ∘ pairCoordinates.symm)) triangle := by
  have hc : ContinuousOn (simplexCoefficient ω S ∘ pairCoordinates.symm) triangle :=
    (simplexCoefficient_continuousOn ω S hω).comp
      pairCoordinates.symm.continuous.continuousOn (by
        intro p hp
        change p ∈ pairCoordinates.symm ⁻¹' standardSimplex 2
        rwa [pairCoordinates_symm_triangle])
  exact hc.congr (fun p hp => (simplexCoefficient_pair ω S hp).symm)

/-- The pair-coordinate outer source integral has the existing Euclidean form
integral as value. `triangle_source` also supplies each inner source witness. -/
theorem simplexIntegral_triangle_source (ω : Form 2 E) (S : SmoothSimplex 2 E)
    (hω : ContinuousOn ω (S.toFun '' standardSimplex 2)) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..1, triangleZeroExtension
        (triangleCoefficient ω (S.toFun ∘ pairCoordinates.symm)) (x,y)) id 0 1
      (simplexIntegral ω S) := by
  rw [simplexIntegral_eq_formIntegral ω S hω]
  exact (triangle_source _ (triangleCoefficient_continuousOn ω S hω)).2

/-- Repeated integration, eliminating coordinate zero first. The zero-dimensional
integral is evaluation. This definition alone makes no integrability assertion. -/
def iterated (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ :=
  Nat.rec (motive := fun n => (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ)
    (fun _ _ f => f 0)
    (fun _ ih a b f => ih (fun i => a i.succ) (fun i => b i.succ)
      (fun x => ∫ t in a 0..b 0, f (Fin.cons t x))) n

/-- Every one-dimensional integration has the literal source Darboux value,
for every remaining parameter, not merely almost every parameter. -/
def HasSourceIntegral (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) →
    ((Fin n → ℝ) → ℝ) → ℝ → Prop :=
  Nat.rec (motive := fun n => (Fin n → ℝ) → (Fin n → ℝ) →
      ((Fin n → ℝ) → ℝ) → ℝ → Prop)
    (fun _ _ f v => f 0 = v)
    (fun _ ih a b f v =>
      (∀ x ∈ Icc (fun i => a i.succ) (fun i => b i.succ),
        StieltjesPrototype.HasDarbouxRSIntegral (fun t => f (Fin.cons t x)) id
          (a 0) (b 0) (∫ t in a 0..b 0, f (Fin.cons t x))) ∧
      ih (fun i => a i.succ) (fun i => b i.succ)
        (fun x => ∫ t in a 0..b 0, f (Fin.cons t x)) v) n

theorem cons_mem_Icc {n : ℕ} {a b : Fin (n+1) → ℝ} {t : ℝ} {x : Fin n → ℝ} :
    Fin.cons t x ∈ Icc a b ↔
      t ∈ Icc (a 0) (b 0) ∧ x ∈ Icc (fun i => a i.succ) (fun i => b i.succ) := by
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  tauto

/-- Both repeated values and source witnesses depend only on the closed box. -/
theorem iterated_congr {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f g : (Fin n → ℝ) → ℝ} (h : EqOn f g (Icc a b)) :
    iterated n a b f = iterated n a b g := by
  induction n with
  | zero => exact h ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    apply ih (fun i => hab i.succ)
    intro x hx
    apply intervalIntegral.integral_congr
    intro t ht
    exact h (cons_mem_Icc.mpr ⟨by simpa [uIcc_of_le (hab 0)] using ht, hx⟩)

theorem source_congr {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f g : (Fin n → ℝ) → ℝ} {v : ℝ} (h : EqOn f g (Icc a b))
    (hf : HasSourceIntegral n a b f v) : HasSourceIntegral n a b g v := by
  induction n with
  | zero => exact (h ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩).symm.trans hf
  | succ n ih =>
    have he (x) (hx : x ∈ Icc (fun i => a i.succ) (fun i => b i.succ)) :
        (∫ t in a 0..b 0, f (Fin.cons t x)) = ∫ t in a 0..b 0, g (Fin.cons t x) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact h (cons_mem_Icc.mpr ⟨by simpa [uIcc_of_le (hab 0)] using ht, hx⟩)
    constructor
    · intro x hx
      rw [← he x hx]
      exact StieltjesIntegralLaws.hasDarbouxRSIntegral_congr (hab 0) (hf.1 x hx)
        (fun t ht => h (cons_mem_Icc.mpr ⟨ht,hx⟩))
    · exact ih (fun i => hab i.succ) he hf.2

/-- Continuity of the first marginal, from parameter-integral continuity. -/
theorem marginal_continuous {n : ℕ} (a b : ℝ) {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Continuous f) : Continuous (fun x : Fin n → ℝ =>
      ∫ t in a..b, f (Fin.cons t x)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf.comp (by fun_prop)

/-- Source existence on boxes for ambient continuous coefficients. -/
theorem source_of_continuous {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    HasSourceIntegral n a b f (iterated n a b f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    constructor
    · intro x _
      have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id (hab 0)
        (show ContinuousOn (fun t => f (Fin.cons t x)) (Icc (a 0) (b 0)) from
          (hf.comp (by fun_prop)).continuousOn)
      simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
        ← Real.volume_eq_stieltjes_id] using h
    · exact ih (fun i => hab i.succ) (marginal_continuous _ _ hf)

/-- The source comparison includes degenerate boxes and dimension zero. -/
theorem source_of_continuousOn {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Icc a b)) :
    HasSourceIntegral n a b f (iterated n a b f) := by
  obtain ⟨g, hg, he⟩ := continuous_extension isClosed_Icc hf
  rw [← iterated_congr hab he]
  exact source_congr hab he (source_of_continuous hab hg)

/-- The actual coordinate split, with no volume factor. -/
theorem split_box_integral {n : ℕ} {a b : Fin (n+1) → ℝ}
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : IntegrableOn f (Icc a b)) :
    (∫ x in Icc a b, f x) =
      ∫ x in Icc (fun i => a i.succ) (fun i => b i.succ),
        ∫ t in Icc (a 0) (b 0), f (Fin.cons t x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hs : e.symm ⁻¹' Icc a b =
      Icc (a 0) (b 0) ×ˢ Icc (fun i => a i.succ) (fun i => b i.succ) := by
    ext p
    simpa only [e, mem_preimage, mem_prod,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq] using
      (cons_mem_Icc (a := a) (b := b) (t := p.1) (x := p.2))
  have hi := (hm.integrableOn_comp_preimage e.symm.measurableEmbedding).mpr hf
  have he := hm.setIntegral_preimage_emb e.symm.measurableEmbedding f (Icc a b)
  rw [hs] at hi he
  rw [← he]
  have hh : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Icc (a 0) (b 0))).prod
        (volume.restrict (Icc (fun i => a i.succ) (fun i => b i.succ)))) := by
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Function.comp_def, IntegrableOn, Measure.prod_restrict,
      ← Measure.volume_eq_prod] using hi
  simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Measure.prod_restrict, ← Measure.volume_eq_prod] using
    integral_prod_symm _ hh

/-- Fubini is used only after integrability on the compact box is proved. -/
theorem box_integral_eq_iterated {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Icc a b)) :
    (∫ x in Icc a b, f x) = iterated n a b f := by
  obtain ⟨g, hg, he⟩ := continuous_extension isClosed_Icc hf
  rw [← setIntegral_congr_fun measurableSet_Icc he, ← iterated_congr hab he]
  clear hf he f
  induction n with
  | zero =>
    have hs : Icc a b = (univ : Set (Fin 0 → ℝ)) := by ext x; simp
    simp [hs, iterated, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n ih =>
    rw [split_box_integral (hg.continuousOn.integrableOn_compact isCompact_Icc)]
    simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab 0)]
    exact ih (fun i => hab i.succ) _ (marginal_continuous _ _ hg)

/-- Relabeling coordinates by `σ`; the old coordinate `σ i` has new index `i`.
The inverse in the action on vectors is necessary for this convention. -/
def coordinatePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) σ

@[simp] theorem coordinatePermutation_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (i : Fin n) : coordinatePermutation σ x i = x (σ.symm i) := by
  simp [coordinatePermutation, ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply]

theorem permutation_volume {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (coordinatePermutation σ) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℝ) σ

theorem permutation_preimage_box {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Fin n → ℝ) :
    coordinatePermutation σ ⁻¹' Icc a b = Icc (a ∘ σ) (b ∘ σ) := by
  ext x
  constructor
  · intro h
    exact ⟨fun i => by simpa using h.1 (σ i), fun i => by simpa using h.2 (σ i)⟩
  · intro h
    exact ⟨fun i => by simpa using h.1 (σ.symm i),
      fun i => by simpa using h.2 (σ.symm i)⟩

/-- Every coordinate order has source Darboux witnesses and the same value.
The comparison is derived from Fubini and measure-preserving relabeling. -/
theorem box_source_all_orders {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Icc a b))
    (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ)
      (∫ x in Icc a b, f x) ∧
    iterated n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ) = iterated n a b f := by
  have hc : ContinuousOn (f ∘ coordinatePermutation σ) (Icc (a ∘ σ) (b ∘ σ)) :=
    hf.comp (coordinatePermutation σ).continuous.continuousOn (by
      intro x hx
      exact show x ∈ coordinatePermutation σ ⁻¹' Icc a b from
        permutation_preimage_box σ a b ▸ hx)
  have h := (permutation_volume σ).setIntegral_preimage_emb
    (coordinatePermutation σ).toHomeomorph.measurableEmbedding f (Icc a b)
  rw [permutation_preimage_box] at h
  have hv := (box_integral_eq_iterated (a := a ∘ σ) (b := b ∘ σ)
    (fun i => hab (σ i)) hc).symm.trans h
  exact ⟨hv ▸ source_of_continuousOn (fun i => hab (σ i)) hc,
    hv.trans (box_integral_eq_iterated hab hf)⟩

/-- Pinned BoxIntegral Riemann sums have the proved source repeated value.
This comparison applies to nondegenerate `Box`; source boxes above may degenerate. -/
theorem boxIntegral_source {n : ℕ} (I : BoxIntegral.Box (Fin n))
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (BoxIntegral.Box.Icc I)) :
    BoxIntegral.HasIntegral I BoxIntegral.IntegrationParams.Riemann f
      (volume : Measure (Fin n → ℝ)).toBoxAdditive.toSMul
      (iterated n I.lower I.upper f) := by
  have h := hf.hasBoxIntegral volume BoxIntegral.IntegrationParams.Riemann
  have he : (∫ x in (I : Set (Fin n → ℝ)), f x) = ∫ x in Icc I.lower I.upper, f x := by
    apply setIntegral_congr_set
    rw [BoxIntegral.Box.coe_eq_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc
  rw [he, box_integral_eq_iterated I.lower_le_upper hf] at h
  exact h

/-- Actual Euclidean box volume, in arbitrary dimension. -/
theorem euclidean_box_volume {n : ℕ} (a b : Fin n → ℝ) :
    volume ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [(coordinates_volume n).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]

/-- The Euclidean set integral has source Darboux witnesses in every coordinate
order. The product-volume normalization is proved by `coordinates_symm_volume`. -/
theorem euclidean_box_source {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b))
    (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n (a ∘ σ) (b ∘ σ)
      (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation σ)
      (∫ u in (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b, f u) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hc : ContinuousOn (f ∘ e.symm) (Icc a b) :=
    hf.comp e.symm.continuous.continuousOn (by
      intro x hx
      change e (e.symm x) ∈ Icc a b
      simpa only [e.apply_symm_apply] using hx)
  have h := (coordinates_volume n).setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (f ∘ e.symm) (Icc a b)
  change (∫ x in e ⁻¹' Icc a b, f (e.symm (e x))) = _ at h
  simp only [e.symm_apply_apply] at h
  rw [h]
  exact (box_source_all_orders hab hc σ).1

/-- The closed standard simplex in product coordinates. -/
def piSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The literal zero extension, retaining all boundary values. -/
def simplexZeroExtension {n : ℕ} (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  (piSimplex n).indicator f

@[simp] theorem coordinates_simplex (n : ℕ) :
    (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' piSimplex n = standardSimplex n := rfl

@[simp] theorem coordinates_symm_simplex (n : ℕ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹' standardSimplex n = piSimplex n := rfl

theorem piSimplex_isCompact (n : ℕ) : IsCompact (piSimplex n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isCompact_preimage.mpr
    (standardSimplex_isCompact n)

theorem piSimplex_subset_cube (n : ℕ) : piSimplex n ⊆ Icc 0 1 := by
  intro x hx
  exact ⟨hx.1, fun i => (Finset.single_le_sum (fun j _ => hx.1 j)
    (Finset.mem_univ i)).trans hx.2⟩

/-- Integrability of the zero extension follows from compactness of the simplex,
not from the total Bochner integral convention. -/
theorem simplexZeroExtension_integrable {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex n)) : Integrable (simplexZeroExtension f) :=
  (integrable_indicator_iff (piSimplex_isCompact n).measurableSet).mpr
    (hf.integrableOn_compact (piSimplex_isCompact n))

/-- The length of a simplex fiber, clipped at zero outside its projection. -/
def fiberLength {n : ℕ} (x : Fin n → ℝ) : ℝ := max 0 (1 - ∑ i, x i)

theorem fiberLength_continuous (n : ℕ) : Continuous (@fiberLength n) := by
  unfold fiberLength
  fun_prop

/-- On the projected simplex, the zero-extension row is exactly a closed cut. -/
theorem simplex_slice_cut {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ Icc 0 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    simplexZeroExtension f (Fin.cons t x) =
      (Iic (1 - ∑ i, x i)).indicator (fun t => f (Fin.cons t x)) t := by
  have hm : Fin.cons t x ∈ piSimplex (n+1) ↔ t ≤ 1 - ∑ i, x i := by
    simp only [piSimplex, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.sum_univ_succ]
    constructor
    · intro h; linarith [h.2]
    · intro h; exact ⟨⟨ht.1, hx.1⟩, by linarith⟩
  simp only [simplexZeroExtension, indicator, hm, mem_Iic]

/-- Outside the projected simplex the whole row is zero, even at endpoints. -/
theorem simplex_slice_zero {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    {x : Fin n → ℝ} (hs : 1 < ∑ i, x i) {t : ℝ} (ht : 0 ≤ t) :
    simplexZeroExtension f (Fin.cons t x) = 0 := by
  apply indicator_of_notMem
  intro h
  have hh := h.2
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hh
  linarith

/-- Every fiber has a source Darboux integral, and its measure integral has that
value. In particular, fibers of length zero do not lose their endpoint values. -/
theorem simplex_fiber_source {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} (hf : Continuous f)
    {x : Fin n → ℝ} (hx : x ∈ Icc 0 1) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun t => simplexZeroExtension f (Fin.cons t x)) id 0 1
      (∫ t in 0..fiberLength x, f (Fin.cons t x)) ∧
    (∫ t in 0..1, simplexZeroExtension f (Fin.cons t x)) =
      ∫ t in 0..fiberLength x, f (Fin.cons t x) := by
  by_cases hs : ∑ i, x i ≤ 1
  · have hc : 1 - ∑ i, x i ∈ Icc (0 : ℝ) 1 :=
      ⟨sub_nonneg.mpr hs, by
        have hn : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx.1 i)
        linarith⟩
    have he : EqOn (fun t => (Iic (1 - ∑ i, x i)).indicator
        (fun t => f (Fin.cons t x)) t)
        (fun t => simplexZeroExtension f (Fin.cons t x)) (Icc 0 1) :=
      fun t ht => (simplex_slice_cut f hx ht).symm
    rw [fiberLength, max_eq_right hc.1]
    constructor
    · exact StieltjesIntegralLaws.hasDarbouxRSIntegral_congr (by norm_num)
        (cut_darboux _ (hf.comp (by fun_prop)) hc) he
    · calc
        _ = ∫ t in 0..1, (Iic (1 - ∑ i, x i)).indicator
            (fun t => f (Fin.cons t x)) t := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact (he (by simpa using ht)).symm
        _ = _ := intervalIntegral.integral_indicator hc
  · have he : EqOn (fun _ : ℝ => (0 : ℝ))
        (fun t => simplexZeroExtension f (Fin.cons t x)) (Icc 0 1) :=
      fun t ht => (simplex_slice_zero f (lt_of_not_ge hs) ht.1).symm
    rw [fiberLength, max_eq_left (by linarith : 1 - ∑ i, x i ≤ 0),
      intervalIntegral.integral_same]
    constructor
    · have h := cut_darboux (fun _ : ℝ => (0 : ℝ)) continuous_const
        (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      have hz : (Iic (0 : ℝ)).indicator (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
        funext t
        simp
      rw [hz, intervalIntegral.integral_zero] at h
      exact StieltjesIntegralLaws.hasDarbouxRSIntegral_congr (by norm_num) h he
    · calc
        _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact (he (by simpa using ht)).symm
        _ = 0 := intervalIntegral.integral_zero

/-- After the first integration, the simplex zero extension has a continuous
marginal on the entire remaining cube. This is the key source-existence step. -/
theorem simplex_marginal_continuousOn {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Continuous f) : ContinuousOn
      (fun x : Fin n → ℝ => ∫ t in 0..1, simplexZeroExtension f (Fin.cons t x))
      (Icc 0 1) := by
  have hc : Continuous (fun x : Fin n → ℝ => ∫ t in 0..fiberLength x, f (Fin.cons t x)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun x t => f (Fin.cons t x))
      (hf.comp (by fun_prop)) (fiberLength_continuous n)
  exact hc.continuousOn.congr (fun x hx => (simplex_fiber_source hf hx).2)

/-- Example 10.4 in any dimension: every source stage exists, and Fubini
identifies its value with the simplex set integral. -/
theorem simplex_source {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex n)) :
    HasSourceIntegral n 0 1 (simplexZeroExtension f) (∫ x in piSimplex n, f x) ∧
    iterated n 0 1 (simplexZeroExtension f) = ∫ x in piSimplex n, f x := by
  obtain ⟨g, hg, he⟩ := continuous_extension (piSimplex_isCompact n).isClosed hf
  have hz : simplexZeroExtension g = simplexZeroExtension f := indicator_congr he
  have hv : (∫ x in piSimplex n, g x) = ∫ x in piSimplex n, f x :=
    setIntegral_congr_fun (piSimplex_isCompact n).measurableSet he
  rw [← hz, ← hv]
  clear hz hv he hf f
  have hi := simplexZeroExtension_integrable hg.continuousOn
  have he : (∫ x in Icc (0 : Fin n → ℝ) 1, simplexZeroExtension g x) =
      ∫ x in piSimplex n, g x := by
    rw [simplexZeroExtension, setIntegral_indicator (piSimplex_isCompact n).measurableSet,
      inter_eq_right.mpr (piSimplex_subset_cube n)]
  cases n with
  | zero =>
    have hs : piSimplex 0 = univ := by ext x; simp [piSimplex]
    simp [HasSourceIntegral, iterated, simplexZeroExtension, hs,
      Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n =>
    have hc := simplex_marginal_continuousOn hg
    have hv : (∫ x in piSimplex (n+1), g x) =
        iterated n 0 1 (fun x => ∫ t in 0..1, simplexZeroExtension g (Fin.cons t x)) := by
      rw [← he, split_box_integral hi.integrableOn]
      change (∫ x in Icc (0 : Fin n → ℝ) 1, ∫ t in Icc (0 : ℝ) 1,
        simplexZeroExtension g (Fin.cons t x)) = _
      simp_rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact box_integral_eq_iterated (by intro i; norm_num) hc
    constructor
    · constructor
      · intro x hx
        change StieltjesPrototype.HasDarbouxRSIntegral _ id 0 1
          (∫ t in 0..1, simplexZeroExtension g (Fin.cons t x))
        rw [(simplex_fiber_source hg hx).2]
        exact (simplex_fiber_source hg hx).1
      · rw [hv]
        exact source_of_continuousOn (by intro i; norm_num) hc
    · exact hv.symm

/-- Coordinate permutations preserve the closed simplex, including its faces. -/
theorem permutation_preimage_simplex {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    coordinatePermutation σ ⁻¹' piSimplex n = piSimplex n := by
  ext x
  have hs : ∑ i, coordinatePermutation σ x i = ∑ i, x i := by
    simp only [coordinatePermutation_apply]
    exact Equiv.sum_comp σ.symm x
  change ((∀ i, 0 ≤ coordinatePermutation σ x i) ∧
    ∑ i, coordinatePermutation σ x i ≤ 1) ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1
  rw [hs]
  simp only [coordinatePermutation_apply]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h.1 (σ i), h.2⟩
  · intro h
    exact ⟨fun i => h.1 (σ.symm i), h.2⟩

theorem simplexZeroExtension_permutation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ) :
    simplexZeroExtension (f ∘ coordinatePermutation σ) =
      simplexZeroExtension f ∘ coordinatePermutation σ := by
  classical
  funext x
  have hm : coordinatePermutation σ x ∈ piSimplex n ↔ x ∈ piSimplex n := by
    change x ∈ coordinatePermutation σ ⁻¹' piSimplex n ↔ _
    rw [permutation_preimage_simplex]
  change (if x ∈ piSimplex n then f (coordinatePermutation σ x) else 0) =
    if coordinatePermutation σ x ∈ piSimplex n then f (coordinatePermutation σ x) else 0
  rw [hm]

/-- Arbitrary-dimensional order independence for the literal zero extension.
All one-dimensional source integrals exist at every remaining parameter. -/
theorem simplex_source_all_orders {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex n)) (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n 0 1 (simplexZeroExtension f ∘ coordinatePermutation σ)
      (∫ x in piSimplex n, f x) ∧
    iterated n 0 1 (simplexZeroExtension f ∘ coordinatePermutation σ) =
      iterated n 0 1 (simplexZeroExtension f) := by
  have hc : ContinuousOn (f ∘ coordinatePermutation σ) (piSimplex n) :=
    hf.comp (coordinatePermutation σ).continuous.continuousOn (by
      intro x hx
      change x ∈ coordinatePermutation σ ⁻¹' piSimplex n
      rw [permutation_preimage_simplex]
      exact hx)
  have he := (permutation_volume σ).setIntegral_preimage_emb
    (coordinatePermutation σ).toHomeomorph.measurableEmbedding f (piSimplex n)
  rw [permutation_preimage_simplex] at he
  obtain ⟨hi, hv⟩ := simplex_source hc
  rw [simplexZeroExtension_permutation] at hi hv
  exact ⟨he ▸ hi, hv.trans (he.trans (simplex_source hf).2.symm)⟩

/-- Euclidean volume, the literal zero extension and every source integration
order agree. Continuity is needed only on the compact simplex. -/
theorem euclidean_simplex_source {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f (standardSimplex n)) (σ : Equiv.Perm (Fin n)) :
    IntegrableOn f (standardSimplex n) ∧
    HasSourceIntegral n 0 1
      (simplexZeroExtension (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘
        coordinatePermutation σ) (∫ u in standardSimplex n, f u) ∧
    iterated n 0 1
      (simplexZeroExtension (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘
        coordinatePermutation σ) = ∫ u in standardSimplex n, f u := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hc : ContinuousOn (f ∘ e.symm) (piSimplex n) :=
    hf.comp e.symm.continuous.continuousOn (fun _ hx => hx)
  have he := (coordinates_symm_volume n).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding f (standardSimplex n)
  rw [coordinates_symm_simplex] at he
  obtain ⟨hi, hv⟩ := simplex_source_all_orders hc σ
  refine ⟨hf.integrableOn_compact (standardSimplex_isCompact n), he ▸ hi, ?_⟩
  exact hv.trans ((simplex_source hc).2.trans he)

/-- General simplex-form integration now has source witnesses, with the actual
pullback coefficient and its derived continuity. No chain descent is implied. -/
theorem simplexIntegral_source {n : ℕ} (ω : Form n E) (S : SmoothSimplex n E)
    (hω : ContinuousOn ω (S.toFun '' standardSimplex n)) (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n 0 1
      (simplexZeroExtension (simplexCoefficient ω S ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ coordinatePermutation σ)
      (simplexIntegral ω S) :=
  (euclidean_simplex_source (simplexCoefficient_continuousOn ω S hω) σ).2.1

/-- A source witness cannot certify a different value from its repeated integral. -/
theorem HasSourceIntegral.value {n : ℕ} {a b : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {v : ℝ} (h : HasSourceIntegral n a b f v) :
    iterated n a b f = v := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.2

/-- A source witness has a unique value, including dimension zero. -/
theorem HasSourceIntegral.unique {n : ℕ} {a b : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {v w : ℝ} (hv : HasSourceIntegral n a b f v)
    (hw : HasSourceIntegral n a b f w) : v = w := hv.value.symm.trans hw.value

/-- The parameter simplex is convex in its actual product coordinates. -/
theorem piSimplex_convex (n : ℕ) : Convex ℝ (piSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

/-- The discontinuities introduced by zero extension lie on a null frontier. -/
theorem simplexZeroExtension_ae_continuous {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex n)) :
    ∀ᵐ x ∂volume, ContinuousAt (simplexZeroExtension f) x := by
  obtain ⟨g, hg, he⟩ := continuous_extension (piSimplex_isCompact n).isClosed hf
  have hz : simplexZeroExtension g = simplexZeroExtension f := indicator_congr he
  rw [← hz]
  have hn : ∀ᵐ x : Fin n → ℝ ∂volume, x ∉ frontier (piSimplex n) := by
    rw [ae_iff]
    simpa using (piSimplex_convex n).addHaar_frontier volume
  filter_upwards [hn] with x hx
  by_cases hs : x ∈ piSimplex n
  · have hi : x ∈ interior (piSimplex n) := (mem_interior_iff_notMem_frontier hs).mpr hx
    apply hg.continuousAt.congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hi] with y hy
    exact indicator_of_mem (interior_subset hy) g
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(piSimplex_isCompact n).isClosed.isOpen_compl.mem_nhds hs] with y hy
    exact indicator_of_notMem hy g

/-- The nondegenerate unit box used for the literal zero extension. -/
def unitBox (n : ℕ) : BoxIntegral.Box (Fin n) := ⟨0, 1, fun _ => by norm_num⟩

/-- The pinned tagged Riemann integral of the zero extension has the proved
source value. Boundary values are retained; nullity is used only in comparison. -/
theorem simplex_boxIntegral {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex n)) :
    BoxIntegral.HasIntegral (unitBox n) BoxIntegral.IntegrationParams.Riemann
      (simplexZeroExtension f) (volume : Measure (Fin n → ℝ)).toBoxAdditive.toSMul
      (iterated n 0 1 (simplexZeroExtension f)) := by
  obtain ⟨M, hM⟩ := (piSimplex_isCompact n).exists_bound_of_continuousOn hf
  have hb : ∃ C : ℝ, ∀ x ∈ BoxIntegral.Box.Icc (unitBox n),
      ‖simplexZeroExtension f x‖ ≤ C := by
    refine ⟨max M 0, fun x _ => ?_⟩
    by_cases hx : x ∈ piSimplex n
    · rw [simplexZeroExtension, indicator_of_mem hx]
      exact (hM x hx).trans (le_max_left M 0)
    · simp only [simplexZeroExtension, indicator_of_notMem hx, norm_zero]
      exact le_max_right M 0
  have h := AEContinuous.hasBoxIntegral volume hb
    (simplexZeroExtension_ae_continuous hf) BoxIntegral.IntegrationParams.Riemann
  have he : (∫ x in (unitBox n : Set (Fin n → ℝ)), simplexZeroExtension f x) =
      ∫ x in piSimplex n, f x := by
    calc
      _ = ∫ x in Icc (0 : Fin n → ℝ) 1, simplexZeroExtension f x := by
        apply setIntegral_congr_set
        rw [BoxIntegral.Box.coe_eq_pi]
        exact Measure.univ_pi_Ioc_ae_eq_Icc
      _ = _ := by
        rw [simplexZeroExtension, setIntegral_indicator (piSimplex_isCompact n).measurableSet,
          inter_eq_right.mpr (piSimplex_subset_cube n)]
  rw [he, ← (simplex_source hf).2] at h
  exact h

/-- Slice integration on the simplex, with the projected simplex as domain.
This is useful for volume computations and later face-integral arguments. -/
theorem simplex_integral_succ {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} (hf : Continuous f) :
    (∫ x in piSimplex (n+1), f x) =
      ∫ x in piSimplex n, ∫ t in 0..(1 - ∑ i, x i), f (Fin.cons t x) := by
  have he (m : ℕ) (g : (Fin m → ℝ) → ℝ) :
      (∫ x in piSimplex m, g x) = ∫ x in Icc (0 : Fin m → ℝ) 1,
        simplexZeroExtension g x := by
    rw [simplexZeroExtension, setIntegral_indicator (piSimplex_isCompact m).measurableSet,
      inter_eq_right.mpr (piSimplex_subset_cube m)]
  rw [he (n+1) f, split_box_integral (simplexZeroExtension_integrable hf.continuousOn).integrableOn,
    he n]
  change (∫ x in Icc (0 : Fin n → ℝ) 1, ∫ t in Icc (0 : ℝ) 1,
    simplexZeroExtension f (Fin.cons t x)) = _
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [(simplex_fiber_source hf hx).2]
  by_cases hs : ∑ i, x i ≤ 1
  · rw [simplexZeroExtension, indicator_of_mem (show x ∈ piSimplex n from ⟨hx.1,hs⟩)]
    rw [fiberLength, max_eq_right (sub_nonneg.mpr hs)]
  · rw [simplexZeroExtension, indicator_of_notMem (show x ∉ piSimplex n from fun h => hs h.2)]
    rw [fiberLength, max_eq_left (by linarith : 1 - ∑ i, x i ≤ 0),
      intervalIntegral.integral_same]

/-- Moments of the missing barycentric coordinate. The case `k = 0` computes
standard simplex volume, rather than leaving its normalization unspecified. -/
theorem simplex_barycentric_moment (n k : ℕ) :
    (∫ x in piSimplex n, (1 - ∑ i, x i) ^ k) =
      (k.factorial : ℝ) / ((n+k).factorial : ℝ) := by
  induction n generalizing k with
  | zero =>
    have hs : piSimplex 0 = univ := by ext x; simp [piSimplex]
    simp [hs, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), Nat.factorial_ne_zero]
  | succ n ih =>
    rw [simplex_integral_succ (by fun_prop)]
    have hi (x : Fin n → ℝ) :
        (∫ t in 0..(1 - ∑ i, x i), (1 - ∑ i, Fin.cons t x i) ^ k) =
          (1 - ∑ i, x i) ^ (k+1) / (k+1) := by
      have he : (fun t => (1 - ∑ i, Fin.cons t x i) ^ k) =
          fun t => ((1 - ∑ i, x i) - t) ^ k := by
        funext t
        congr 1
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring
      rw [he, intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ k)]
      simp [integral_pow]
    simp_rw [hi]
    rw [integral_div, ih]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hn : (((n+(k+1)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have he : n+1+k = n+(k+1) := by omega
    rw [he]
    field_simp

/-- The geometric volume of the standard product-coordinate simplex is `1/n!`.
Dimension zero has mass one, as required for evaluation of a zero-form. -/
theorem piSimplex_volume (n : ℕ) :
    volume.real (piSimplex n) = 1 / (n.factorial : ℝ) := by
  simpa using simplex_barycentric_moment n 0

/-- The same exact volume in the actual Euclidean metric and volume measure. -/
theorem standardSimplex_volume (n : ℕ) :
    volume.real (standardSimplex n) = 1 / (n.factorial : ℝ) := by
  have h := (coordinates_volume n).measure_preimage (piSimplex_isCompact n).measurableSet.nullMeasurableSet
  rw [coordinates_simplex] at h
  change (volume (standardSimplex n)).toReal = _
  rw [h]
  exact piSimplex_volume n

/-- The ENNReal volume statement also records finiteness explicitly. -/
theorem standardSimplex_measure (n : ℕ) :
    volume (standardSimplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [← standardSimplex_volume n]
  exact (ENNReal.ofReal_toReal (standardSimplex_isCompact n).measure_ne_top).symm

end Rudin.Support.MultivariateRiemann
