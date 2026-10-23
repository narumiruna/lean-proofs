module

public import Math.Rudin.Support.StieltjesMeasureBridge
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-! Exercise 10.29, primary PDF 306/book 297, with Theorem 10.38 on
PDF 287/book 278. All smoothness assertions are local to the open domains. -/
@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise29
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Manifold

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- Projection onto the coordinates preceding the integration coordinate. -/
def projection (V : Set (X × ℝ)) : Set X := Prod.fst '' V

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem projection_open {V : Set (X × ℝ)} (hV : IsOpen V) : IsOpen (projection V) :=
  isOpenMap_fst _ hV

omit [FiniteDimensional ℝ X] in
theorem fiber_convex {V : Set (X × ℝ)} (hV : Convex ℝ V) (x : X) :
    Convex ℝ {t : ℝ | (x,t) ∈ V} := by
  intro t ht u hu a b ha hb hab
  have h := hV ht hu ha hb hab
  change (x, a • t + b • u) ∈ V
  simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] using h

/-- A genuine partition-of-unity selection. Local constants come from openness;
the library theorem constructs a locally finite smooth weighted sum. The empty
projection is allowed. No section is supplied as a hypothesis. -/
theorem section_exists {V : Set (X × ℝ)} (hVo : IsOpen V) (hVc : Convex ℝ V) :
    ∃ α : X → ℝ, ContDiffOn ℝ 1 α (projection V) ∧
      ∀ x ∈ projection V, (x, α x) ∈ V := by
  let : SecondCountableTopology X :=
    (Module.finBasis ℝ X).equivFunL.toHomeomorph.secondCountableTopology
  let U : Opens X := ⟨projection V, projection_open hVo⟩
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hc (x : U) : Convex ℝ {t : ℝ | ((x : X),t) ∈ V} := fiber_convex hVc x
  have hl (x : U) : ∃ c : ℝ, ∀ᶠ y : U in 𝓝 x, ((y : X),c) ∈ V := by
    obtain ⟨⟨z,c⟩, hz, he⟩ := x.property
    have hz' : ((x : X),c) ∈ V := by simpa only [Prod.fst] using he ▸ hz
    refine ⟨c, ?_⟩
    exact (show Continuous (fun y : U => ((y : X),c)) by fun_prop).continuousAt
      (hVo.mem_nhds hz')
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
    (I := 𝓘(ℝ, X)) (n := 1) hc hl
  let α : X → ℝ := Subtype.val.extend g 0
  have he (x : U) : α x = g x := Subtype.val_injective.extend_apply g 0 x
  refine ⟨α, ?_, ?_⟩
  · intro x hx
    have h : ContMDiffAt 𝓘(ℝ, X) 𝓘(ℝ, ℝ) 1 (fun y : U => α y) ⟨x,hx⟩ := by
      have hh : (fun y : U => α y) = g := funext he
      rw [hh]
      exact g.contMDiff.contMDiffAt
    exact (contMDiffAt_iff_contDiffAt.mp (contMDiffAt_subtype_iff.mp h)).contDiffWithinAt
  · intro x hx
    rw [he ⟨x,hx⟩]
    exact hg ⟨x,hx⟩

/-- Integration over a fixed compact interval preserves local C¹ regularity.
The bounds used in differentiation are proved on a compact neighborhood; they
are not hypotheses on the source function. -/
theorem integral_c1_data {O : Set X} (hO : IsOpen O) {H : X × ℝ → ℝ}
    (hH : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 H (x,t)) :
    ∀ x ∈ O,
      ContDiffAt ℝ 1 (fun x => ∫ t in (0 : ℝ)..1, H (x,t)) x ∧
      HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, H (x,t))
        (∫ t in (0 : ℝ)..1,
          (fderiv ℝ H (x,t)).comp (ContinuousLinearMap.inl ℝ X ℝ)) x := by
  let D (p : X × ℝ) : X →L[ℝ] ℝ :=
    (fderiv ℝ H p).comp (ContinuousLinearMap.inl ℝ X ℝ)
  have hD {x : X} (hx : x ∈ O) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      ContinuousAt D (x,t) :=
    ((hH x hx t ht).continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const
  have hiH {x : X} (hx : x ∈ O) : IntervalIntegrable (fun t => H (x,t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact ((hH x hx t ht').continuousAt.comp
      (show ContinuousAt (fun t : ℝ => (x,t)) t by fun_prop)).continuousWithinAt
  have hiD {x : X} (hx : x ∈ O) : IntervalIntegrable (fun t => D (x,t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact ((hD hx ht').comp
      (show ContinuousAt (fun t : ℝ => (x,t)) t by fun_prop)).continuousWithinAt
  have hd {x : X} (hx : x ∈ O) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasFDerivAt (fun x => H (x,t)) (D (x,t)) x := by
    exact ((hH x hx t ht).differentiableAt (by norm_num)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))
  intro x hx
  obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  let K := Metric.closedBall x (δ/2)
  have hKO : K ⊆ O := by
    intro y hy
    apply hδO
    exact lt_of_le_of_lt (show dist y x ≤ δ/2 from hy) (by linarith)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hDc : ContinuousOn D (K ×ˢ Icc (0 : ℝ) 1) := by
    rintro ⟨y,t⟩ ⟨hy,ht⟩
    exact (hD (hKO hy) ht).continuousWithinAt
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hDc
  let B := Metric.ball x (δ/2)
  have hBK : B ⊆ K := Metric.ball_subset_closedBall
  have hBO : B ⊆ O := hBK.trans hKO
  have hB : IsOpen B := Metric.isOpen_ball
  have hBound (y : X) (hy : y ∈ B) (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
      ‖D (y,t)‖ ≤ M := by
    exact hM (y,t) ⟨hBK hy, by simpa using Set.uIoc_subset_uIcc ht⟩
  have hdI (y : X) (hy : y ∈ B) :
      HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, H (x,t))
        (∫ t in (0 : ℝ)..1, D (y,t)) y := by
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := B) (bound := fun _ => M) (hB.mem_nhds hy)
    · filter_upwards [hB.mem_nhds hy] with z hz
      exact (intervalIntegrable_iff.mp (hiH (hBO hz))).aestronglyMeasurable
    · exact hiH (hBO hy)
    · exact (intervalIntegrable_iff.mp (hiD (hBO hy))).aestronglyMeasurable
    · exact Eventually.of_forall (fun t ht z hz => hBound z hz t ht)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall (fun t ht z hz => hd (hBO hz)
        (by simpa using Set.uIoc_subset_uIcc ht))
  have hcI (y : X) (hy : y ∈ B) :
      ContinuousAt (fun x => ∫ t in (0 : ℝ)..1, D (x,t)) y := by
    apply intervalIntegral.continuousAt_of_dominated_interval
      (F := fun z t => D (z,t)) (x₀ := y) (bound := fun _ => M)
    · filter_upwards [hB.mem_nhds hy] with z hz
      exact (intervalIntegrable_iff.mp (hiD (hBO hz))).aestronglyMeasurable
    · filter_upwards [hB.mem_nhds hy] with z hz
      exact Eventually.of_forall (fun t ht => hBound z hz t ht)
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro t ht
      have hc : ContinuousAt D (y,t) :=
        hD (hBO hy) (by simpa using Set.uIoc_subset_uIcc ht)
      exact hc.comp (f := fun z : X => (z,t)) (by fun_prop)
  refine ⟨?_, hdI x (Metric.mem_ball_self (by linarith))⟩
  rw [contDiffAt_one_iff]
  exact ⟨_, B, Metric.ball_mem_nhds _ (by linarith),
    fun y hy => (hcI y hy).continuousWithinAt, hdI⟩

/-- C¹ regularity follows from the actual derivative formula above. -/
theorem integral_c1 {O : Set X} (hO : IsOpen O) {H : X × ℝ → ℝ}
    (hH : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 H (x,t)) :
    ContDiffOn ℝ 1 (fun x => ∫ t in (0 : ℝ)..1, H (x,t)) O :=
  fun x hx => ((integral_c1_data hO hH x hx).1).contDiffWithinAt

/-- The parameter derivative is the integral of the genuine parameter derivative.
The compact bound is derived in `integral_c1_data`, not an extra hypothesis. -/
theorem integral_hasFDerivAt {O : Set X} (hO : IsOpen O) {H : X × ℝ → ℝ}
    (hH : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 H (x,t))
    {x : X} (hx : x ∈ O) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, H (x,t))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℝ H (x,t)).comp (ContinuousLinearMap.inl ℝ X ℝ)) x :=
  (integral_c1_data hO hH x hx).2

omit [FiniteDimensional ℝ X] in
/-- Convex fibers contain the complete integration interval in either order. -/
theorem fiber_interval {V : Set (X × ℝ)} (hV : Convex ℝ V) {x : X} {a b : ℝ}
    (ha : (x,a) ∈ V) (hb : (x,b) ∈ V) :
    ∀ t ∈ uIcc a b, (x,t) ∈ V :=
  (fiber_convex hV x).ordConnected.uIcc_subset ha hb

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- The affine substitution is valid also for zero length and reversed bounds. -/
theorem integral_affine (φ : X × ℝ → ℝ) (x : X) (a b : ℝ) :
    (∫ t in a..b, φ (x,t)) =
      ∫ s in (0 : ℝ)..1, (b-a) * φ (x, a + (b-a)*s) := by
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun t => φ (x,t)) (a := 0) (b := 1) (b-a) a
  simpa only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] using h.symm

/-- Varying lower endpoints require only local C¹ data on the open convex set.
This lemma is used with the section constructed above, not as an input section
for the exercise theorem. -/
theorem varying_integral_c1 {V : Set (X × ℝ)} (hVo : IsOpen V) (hVc : Convex ℝ V)
    {φ : X × ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ V)
    {α : X → ℝ} (hα : ContDiffOn ℝ 1 α (projection V))
    (hαV : ∀ x ∈ projection V, (x,α x) ∈ V) :
    ContDiffOn ℝ 1 (fun p => ∫ t in α p.1..p.2, φ (p.1,t)) V := by
  let H (q : (X × ℝ) × ℝ) : ℝ :=
    (q.1.2 - α q.1.1) * φ (q.1.1, α q.1.1 + (q.1.2 - α q.1.1)*q.2)
  have hH (p : X × ℝ) (hp : p ∈ V) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 H (p,s) := by
    have hx : p.1 ∈ projection V := ⟨p,hp,rfl⟩
    have ha : ContDiffAt ℝ 1 α p.1 := (hα _ hx).contDiffAt ((projection_open hVo).mem_nhds hx)
    have ha' : ContDiffAt ℝ 1 (fun q : (X × ℝ) × ℝ => α q.1.1) (p,s) :=
      ha.comp (p,s) (contDiffAt_fst.fst)
    have hmem : (p.1, α p.1 + (p.2-α p.1)*s) ∈ V := by
      have h := hVc (hαV p.1 hx) hp (sub_nonneg.mpr hs.2) hs.1 (by ring : 1-s+s=1)
      have heq : (p.1, α p.1 + (p.2-α p.1)*s) = (1-s) • (p.1,α p.1) + s • p := by
        apply Prod.ext
        · change p.1 = (1-s) • p.1 + s • p.1
          module
        · change α p.1 + (p.2-α p.1)*s = (1-s)*α p.1 + s*p.2
          ring
      rwa [heq]
    have hmap : ContDiffAt ℝ 1
        (fun q : (X × ℝ) × ℝ => (q.1.1, α q.1.1 + (q.1.2-α q.1.1)*q.2)) (p,s) := by
      exact contDiffAt_fst.fst.prodMk (ha'.add ((contDiffAt_fst.snd.sub ha').mul contDiffAt_snd))
    exact (contDiffAt_fst.snd.sub ha').mul
      (((hφ _ hmem).contDiffAt (hVo.mem_nhds hmem)).comp (p,s) hmap)
  have h := integral_c1 hVo hH
  convert h using 1
  funext p
  exact integral_affine φ p.1 (α p.1) p.2

omit [FiniteDimensional ℝ X] in
/-- Integrability is proved on each actual fiber, not inferred from a total
integral. Only continuity on the source domain is used. -/
theorem fiber_integrable {V : Set (X × ℝ)} (hVc : Convex ℝ V)
    {φ : X × ℝ → ℝ} (hφ : ContinuousOn φ V)
    {x : X} {a b : ℝ} (ha : (x,a) ∈ V) (hb : (x,b) ∈ V) :
    IntervalIntegrable (fun t => φ (x,t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact hφ.comp (by fun_prop) (fiber_interval hVc ha hb)

omit [FiniteDimensional ℝ X] in
/-- Ordinary source Riemann witnesses for both orders of the endpoints.
The second branch states the source convention `∫a..b = -∫b..a`. -/
theorem fiber_source {V : Set (X × ℝ)} (hVc : Convex ℝ V)
    {φ : X × ℝ → ℝ} (hφ : ContinuousOn φ V)
    {x : X} {a b : ℝ} (ha : (x,a) ∈ V) (hb : (x,b) ∈ V) :
    (a ≤ b → Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral
      (fun t => φ (x,t)) id a b (∫ t in a..b, φ (x,t))) ∧
    (b ≤ a → Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral
      (fun t => φ (x,t)) id b a (-(∫ t in a..b, φ (x,t)))) := by
  have hcont : ContinuousOn (fun t => φ (x,t)) (uIcc a b) :=
    hφ.comp (by fun_prop) (fiber_interval hVc ha hb)
  constructor
  · intro hab
    have h := Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab
      (by simpa only [uIcc_of_le hab] using hcont)
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id] using h
  · intro hba
    have h := Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hba
      (by simpa only [uIcc_of_ge hba] using hcont)
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id, intervalIntegral.integral_symm b a, neg_neg] using h

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The source's factor `φ` is C¹ on its projection because `f` is C¹ on E.
A fixed value of the unused coordinates gives a local lift. No global extension
or global derivative bound is assumed. -/
theorem factor_c1 {E : Set (Z × Y)} (hE : IsOpen E)
    {f : (Z × Y) → ℝ} (hf : ContDiffOn ℝ 1 f E)
    {φ : Z → ℝ} (he : ∀ p ∈ E, f p = φ p.1) :
    ContDiffOn ℝ 1 φ (Prod.fst '' E) := by
  rintro p ⟨⟨q,y⟩, hq, rfl⟩
  have hlocal : ContDiffAt ℝ 1 (fun z : Z => f (z,y)) q :=
    ((hf _ hq).contDiffAt (hE.mem_nhds hq)).comp q
      (contDiffAt_id.prodMk contDiffAt_const)
  have hn : ∀ᶠ z : Z in 𝓝 q, (z,y) ∈ E :=
    (show ContinuousAt (fun z : Z => (z,y)) q by fun_prop) (hE.mem_nhds hq)
  have heq : (fun z : Z => f (z,y)) =ᶠ[𝓝 q] φ := hn.mono (fun z hz => he (z,y) hz)
  exact (hlocal.congr_of_eventuallyEq heq.symm).contDiffWithinAt

/-- Exercise 29: construct the section, then prove C¹ regularity of the literal
integral on E, including all unused coordinates `Y`. The equation for `φ` is
exactly its definition in the proof of Theorem 10.38. -/
theorem exercise29 {E : Set ((X × ℝ) × Y)} (hEo : IsOpen E) (hEc : Convex ℝ E)
    {f : ((X × ℝ) × Y) → ℝ} (hf : ContDiffOn ℝ 1 f E)
    {φ : X × ℝ → ℝ} (he : ∀ p ∈ E, f p = φ p.1) :
    ∃ α : X → ℝ, ContDiffOn ℝ 1 α (projection (Prod.fst '' E)) ∧
      (∀ x ∈ projection (Prod.fst '' E), (x,α x) ∈ Prod.fst '' E) ∧
      ContDiffOn ℝ 1 (fun p : (X × ℝ) × Y => ∫ t in α p.1.1..p.1.2, φ (p.1.1,t)) E ∧
      ∀ p ∈ E, IntervalIntegrable (fun t => φ (p.1.1,t)) volume (α p.1.1) p.1.2 := by
  have hVo : IsOpen (Prod.fst '' E) := isOpenMap_fst _ hEo
  have hVc : Convex ℝ (Prod.fst '' E) := hEc.linear_image (LinearMap.fst ℝ (X × ℝ) Y)
  obtain ⟨α,hα,hαV⟩ := section_exists hVo hVc
  have hφ := factor_c1 hEo hf he
  refine ⟨α,hα,hαV,?_,?_⟩
  · exact (varying_integral_c1 hVo hVc hφ hα hαV).comp contDiffOn_fst
      (fun p hp => ⟨p,hp,rfl⟩)
  · intro p hp
    have hv : p.1 ∈ Prod.fst '' E := ⟨p,hp,rfl⟩
    exact fiber_integrable hVc hφ.continuousOn (hαV p.1.1 ⟨p.1,hv,rfl⟩) hv

/-- The `p = 1` primitive uses one fixed lower endpoint. -/
theorem fixed_lower_c1 {V : Set ℝ} (hVo : IsOpen V) (hVc : Convex ℝ V)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ V) {c : ℝ} (hc : c ∈ V) :
    ContDiffOn ℝ 1 (fun x => ∫ t in c..x, φ t) V := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨fun y => (1 : ℝ →L[ℝ] ℝ).smulRight (φ y), V, hVo.mem_nhds hx, ?_, ?_⟩
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp_continuousOn hφ.continuousOn
  · intro y hy
    have hi : IntervalIntegrable φ volume c y :=
      (hφ.continuousOn.mono (hVc.ordConnected.uIcc_subset hc hy)).intervalIntegrable
    exact (intervalIntegral.integral_hasDerivAt_right hi
      (ContinuousOn.stronglyMeasurableAtFilter hVo hφ.continuousOn y hy)
      ((hφ _ hy).contDiffAt (hVo.mem_nhds hy)).continuousAt).hasFDerivAt

/-- For nonempty E, the fixed endpoint is chosen from its projection; no
endpoint is supplied by the caller. All unused coordinates are retained. -/
theorem exercise29_p_one {E : Set (ℝ × Y)} (hEo : IsOpen E) (hEc : Convex ℝ E)
    (hne : E.Nonempty) {f : (ℝ × Y) → ℝ} (hf : ContDiffOn ℝ 1 f E)
    {φ : ℝ → ℝ} (he : ∀ p ∈ E, f p = φ p.1) :
    ∃ c ∈ Prod.fst '' E,
      ContDiffOn ℝ 1 (fun p : ℝ × Y => ∫ t in c..p.1, φ t) E ∧
      ∀ p ∈ E, IntervalIntegrable φ volume c p.1 := by
  obtain ⟨p,hp⟩ := hne
  have hc : p.1 ∈ Prod.fst '' E := ⟨p,hp,rfl⟩
  have hVo : IsOpen (Prod.fst '' E) := isOpenMap_fst _ hEo
  have hVc : Convex ℝ (Prod.fst '' E) := hEc.linear_image (LinearMap.fst ℝ ℝ Y)
  have hφ := factor_c1 hEo hf he
  refine ⟨p.1, hc, ?_, ?_⟩
  · exact (fixed_lower_c1 hVo hVc hφ hc).comp contDiffOn_fst
      (fun q hq => ⟨q,hq,rfl⟩)
  · intro q hq
    exact (hφ.continuousOn.mono
      (hVc.ordConnected.uIcc_subset hc ⟨q,hq,rfl⟩)).intervalIntegrable

/-- An empty domain does not supply an endpoint in its empty projection.
The zero function and every displayed fixed-endpoint primitive are C¹ there. -/
theorem exercise29_empty (φ : ℝ → ℝ) (c : ℝ) :
    (Prod.fst '' (∅ : Set (ℝ × Y))) = ∅ ∧
    ContDiffOn ℝ 1 (fun _ : ℝ × Y => (0 : ℝ)) ∅ ∧
    ContDiffOn ℝ 1 (fun p : ℝ × Y => ∫ t in c..p.1, φ t) ∅ := by
  simp only [image_empty]
  exact ⟨True.intro, contDiffOn_empty, contDiffOn_empty⟩

end Rudin.Chapter10.Exercise29
