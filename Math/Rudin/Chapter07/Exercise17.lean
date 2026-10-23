module

public import Math.Rudin.Chapter07.Exercise16
public import Math.Rudin.Chapter07.Exercise19
public import Math.Rudin.Support.StieltjesIntegralLaws

@[expose] public section

open Set Filter Topology
open scoped Topology

namespace Rudin.Chapter07

/-- Uniform convergence uses one index for every point of the domain. -/
def exercise17_uniform {X Y : Type*} [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, dist (f x) (F n x) < ε

/-- The source's equicontinuity uses one radius for every map and every pair of points. -/
def exercise17_equicontinuous {I X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : I → X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε

theorem exercise17_uniform_iff {X Y : Type*} [MetricSpace Y]
    {F : ℕ → X → Y} {f : X → Y} :
    exercise17_uniform F f ↔ TendstoUniformly F f atTop := by
  simp only [exercise17_uniform, Metric.tendstoUniformly_iff, eventually_atTop]

theorem exercise17_equicontinuous_iff {I X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {F : I → X → Y} : exercise17_equicontinuous F ↔ UniformEquicontinuous F :=
  Metric.uniformEquicontinuous_iff.symm

/-- The extended supremum is zero on an empty domain and permits infinite early errors. -/
theorem exercise17_metric_sup_criterion {X Y : Type*} [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) :
    TendstoUniformly F f atTop ↔
      Tendsto (fun n => ⨆ x, edist (F n x) (f x)) atTop (𝓝 0) := by
  have h := UniformFun.tendsto_iff_tendstoUniformly
    (F := fun n => UniformFun.ofFun (F n)) (f := UniformFun.ofFun f) (p := atTop)
  exact h.symm.trans tendsto_iff_edist_tendsto_0

/-- Uniform limits preserve continuity for arbitrary metric targets. -/
theorem exercise17_metric_continuity {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {F : ℕ → X → Y} {f : X → Y} (hc : ∀ n, Continuous (F n))
    (hu : TendstoUniformly F f atTop) : Continuous f :=
  hu.continuous (Frequently.of_forall hc)

/-- A complete metric target is sufficient for the full uniform Cauchy criterion. -/
theorem exercise17_complete_cauchy {X Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (F : ℕ → X → Y) :
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x, dist (F m x) (F n x) < ε) ↔
      ∃ f, TendstoUniformly F f atTop := by
  constructor
  · intro h
    have hc : UniformCauchySeqOn F atTop univ :=
      Metric.uniformCauchySeqOn_iff.mpr (by simpa using h)
    choose f hf using fun x => cauchySeq_tendsto_of_complete (hc.cauchy_map (mem_univ x))
    exact ⟨f, tendstoUniformlyOn_univ.mp
      (hc.tendstoUniformlyOn_of_tendsto (fun x _ => hf x))⟩
  · rintro ⟨f, hf⟩
    simpa using Metric.uniformCauchySeqOn_iff.mp
      (tendstoUniformlyOn_univ.mpr hf).uniformCauchySeqOn

/-- Ascoli selection for proper metric targets, hence for all Euclidean vector targets. -/
theorem exercise17_vector_selection_subsequence {K Y : Type*} [MetricSpace K]
    [CompactSpace K] [MetricSpace Y] [ProperSpace Y] {F : ℕ → K → Y}
    (he : Equicontinuous F)
    (hb : ∀ x, Bornology.IsBounded (range (fun n => F n x))) :
    ∃ f : K → Y, Continuous f ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n => F (φ n)) f atTop := by
  let G : ℕ → C(K, Y) := fun n => ⟨F n, he.continuous n⟩
  have heG : Equicontinuous (fun g : range G => (g.val : K → Y)) := by
    rw [equicontinuous_iff_range] at he
    exact he.comp (fun g : range G => ⟨g.val, by
      rcases g.property with ⟨n, hn⟩; exact ⟨n, congrArg DFunLike.coe hn⟩⟩)
  have hbG : ∀ x, Bornology.IsBounded ((fun g : C(K, Y) => g x) '' range G) := by
    intro x
    simpa only [← range_comp, Function.comp_def, G, ContinuousMap.coe_mk] using hb x
  obtain ⟨g, _, φ, hφ, hg⟩ := (exercise19_compact_closure hbG heG).isSeqCompact
    (fun n => subset_closure (mem_range_self n))
  exact ⟨g, g.continuous, φ, hφ, ContinuousMap.tendsto_iff_tendstoUniformly.mp hg⟩

/-- The same compactness argument gives a single norm bound for the entire family. -/
theorem exercise17_vector_selection_bound {K E : Type*} [MetricSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [ProperSpace E] {F : ℕ → K → E}
    (he : Equicontinuous F)
    (hb : ∀ x, Bornology.IsBounded (range (fun n => F n x))) :
    ∃ M : ℝ, ∀ n x, ‖F n x‖ ≤ M := by
  let G : ℕ → C(K, E) := fun n => ⟨F n, he.continuous n⟩
  have heG : Equicontinuous (fun g : range G => (g.val : K → E)) := by
    rw [equicontinuous_iff_range] at he
    exact he.comp (fun g : range G => ⟨g.val, by
      rcases g.property with ⟨n, hn⟩; exact ⟨n, congrArg DFunLike.coe hn⟩⟩)
  have hbG : ∀ x, Bornology.IsBounded ((fun g : C(K, E) => g x) '' range G) := by
    intro x
    simpa only [← range_comp, Function.comp_def, G, ContinuousMap.coe_mk] using hb x
  obtain ⟨M, hM⟩ := (exercise19_compact_closure hbG heG).isBounded.exists_norm_le
  exact ⟨M, fun n x => (G n).norm_coe_le_norm x |>.trans
    (hM (G n) (subset_closure (mem_range_self n)))⟩

/-- The double-limit theorem, with an arbitrary nontrivial approach filter supported on `S`. -/
theorem exercise17_complete_limit_interchange_filter {X Y : Type*} [MetricSpace Y]
    [CompleteSpace Y] {S : Set X} {l : Filter X} [NeBot l] (hl : l ≤ 𝓟 S)
    {F : ℕ → X → Y} {f : X → Y} {A : ℕ → Y}
    (hu : TendstoUniformlyOn F f atTop S) (hA : ∀ n, Tendsto (F n) l (𝓝 (A n))) :
    ∃ L, Tendsto A atTop (𝓝 L) ∧ Tendsto f l (𝓝 L) := by
  have hc : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu.uniformCauchySeqOn
      (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)⟩
    exact le_of_tendsto ((hA m).dist (hA n))
      ((show ∀ᶠ x in l, x ∈ S from hl (by simp)).mono
        (fun x hx => (hN m hm n hn x hx).le))
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨L, hL, (hu.tendstoUniformlyOnFilter.mono_right hl).tendsto_of_eventually_tendsto
    (Eventually.of_forall hA) hL⟩

/-- At a domain limit point, both iterated limits exist and are equal. -/
theorem exercise17_complete_limit_interchange {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {S : Set X} {x : X} (hx : AccPt x (𝓟 S))
    {F : ℕ → X → Y} {f : X → Y} {A : ℕ → Y}
    (hu : TendstoUniformlyOn F f atTop S)
    (hA : ∀ n, Tendsto (F n) (𝓝[S \ {x}] x) (𝓝 (A n))) :
    ∃ L, Tendsto A atTop (𝓝 L) ∧ Tendsto f (𝓝[S \ {x}] x) (𝓝 L) := by
  have hne : NeBot (𝓝[S \ {x}] x) := by
    simpa only [AccPt, nhdsWithin, sdiff_eq, ← inf_principal, inf_assoc,
      inf_left_comm, inf_comm] using hx
  exact exercise17_complete_limit_interchange_filter (l := 𝓝[S \ {x}] x)
    (inf_le_right.trans (principal_mono.mpr sdiff_subset)) hu hA

/-- The vector majorant test starts with convergence of ordered real partial sums. -/
theorem exercise17_vector_majorant {X E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → X → E} {M : ℕ → ℝ} {L : ℝ}
    (hM : Tendsto (fun n => ∑ i ∈ Finset.range n, M i) atTop (𝓝 L))
    (hb : ∀ n x, ‖F n x‖ ≤ M n) :
    TendstoUniformly (fun n x => ∑ i ∈ Finset.range n, F i x)
      (fun x => ∑' i, F i x) atTop := by
  cases isEmpty_or_nonempty X with
  | inl h =>
    exact Metric.tendstoUniformly_iff.mpr (fun ε _ => Eventually.of_forall
      (fun _ x => isEmptyElim x))
  | inr h =>
    have hn : ∀ n, 0 ≤ M n := fun n => (norm_nonneg (F n (Classical.choice h))).trans
      (hb n (Classical.choice h))
    have hs : Summable M := (summable_iff_not_tendsto_nat_atTop_of_nonneg hn).mpr
      (not_tendsto_nhds_of_tendsto_atTop · _ hM)
    exact tendstoUniformly_tsum_nat hs hb

/-- Uniformly convergent continuous maps on a compact metric domain form a uniformly
 equicontinuous family. This is stronger than the Euclidean vector assertion. -/
theorem exercise17_vector_equicontinuity {K Y : Type*} [MetricSpace K] [CompactSpace K]
    [MetricSpace Y] {F : ℕ → K → Y} {f : K → Y}
    (hc : ∀ n, Continuous (F n)) (hu : TendstoUniformly F f atTop) :
    exercise17_equicontinuous F := by
  let G : ℕ → C(K, Y) := fun n => ⟨F n, hc n⟩
  let g : C(K, Y) := ⟨f, exercise17_metric_continuity hc hu⟩
  have hg : Tendsto G atTop (𝓝 g) := ContinuousMap.tendsto_iff_tendstoUniformly.mpr hu
  have he := exercise19_necessity_equicontinuous hg.isCompact_insert_range
  have hF : Equicontinuous F := he.comp (fun n =>
    (⟨G n, mem_insert_of_mem _ (mem_range_self n)⟩ : ↑(insert g (range G))))
  exact exercise17_equicontinuous_iff.mpr
    (CompactSpace.uniformEquicontinuous_of_equicontinuous hF)

open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesIntegralLaws

/-- A uniform error in an integrand bounds every actual tagged sum. -/
private theorem exercise17_tagged_error {a b δ : ℝ} {α f g : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (p : Partition a b) {tag : ℕ → ℝ}
    (ht : IsTag p tag) (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ δ) :
    |taggedSum p f α tag - taggedSum p g α tag| ≤ δ * (α b - α a) := by
  have hsub : taggedSum p (fun x => f x - g x) α tag =
      taggedSum p f α tag - taggedSum p g α tag := by
    simp [taggedSum, sub_mul, Finset.sum_sub_distrib]
  have h₁ := taggedSum_mono p hα
    (fun x hx => (abs_le.mp (hfg x hx)).1) ht
  have h₂ := taggedSum_mono p hα
    (fun x hx => (abs_le.mp (hfg x hx)).2) ht
  rw [taggedSum_const, hsub] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, h₂⟩

/-- The real tagged Stieltjes uniform-limit theorem. Integral convergence is proved,
 not supplied as an assumption. No continuity of the integrator is required. -/
theorem exercise17_stieltjes_uniform_limit {a b : ℝ} (hab : a ≤ b)
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b))
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {v : ℕ → ℝ}
    (hF : ∀ n, HasRSIntegral (F n) α a b (v n))
    (hu : TendstoUniformlyOn F f atTop (Icc a b)) :
    ∃ L, HasRSIntegral f α a b L ∧ Tendsto v atTop (𝓝 L) := by
  let D := α b - α a
  have hD : 0 ≤ D := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have hc : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let δ := ε / (2 * (D + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ * D < ε := by
      have : δ * (2 * (D + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu.uniformCauchySeqOn δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact (hasRSIntegral_abs_le (hasRSIntegral_sub (hF m) (hF n))
      (fun x hx => (show |F m x - F n x| < δ by
        simpa only [Real.dist_eq] using hN m hm n hn x hx).le)).trans_lt hδε
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, ⟨hα, ?_, ?_⟩, hL⟩
  · obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one).exists
    obtain ⟨M, hM⟩ := (hF n).2.1
    refine ⟨M + 1, fun x hx => ?_⟩
    have he : |f x - F n x| < 1 := by simpa only [Real.dist_eq] using hn x hx
    have := hM x hx
    simpa only [sub_add_cancel] using
      (abs_add_le (f x - F n x) (F n x)).trans (by linarith :
        |f x - F n x| + |F n x| ≤ M + 1)
  · intro ε hε
    let δ := ε / (3 * (D + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ * D < ε / 3 := by
      have : δ * (3 * (D + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    obtain ⟨n, hn, hnL⟩ := ((Metric.tendstoUniformlyOn_iff.mp hu δ hδ).and
      (Metric.tendsto_nhds.mp hL (ε / 3) (by positivity))).exists
    obtain ⟨p, hp⟩ := (hF n).2.2 (ε / 3) (by positivity)
    refine ⟨p, fun q hq tag ht => ?_⟩
    have he := exercise17_tagged_error hα q ht (fun x hx =>
      (show |f x - F n x| < δ by simpa only [Real.dist_eq] using hn x hx).le)
    have hi := hp q hq tag ht
    have hv : |v n - L| < ε / 3 := by simpa only [Real.dist_eq] using hnL
    calc
      |taggedSum q f α tag - L| ≤
          |taggedSum q f α tag - taggedSum q (F n) α tag| +
          |taggedSum q (F n) α tag - v n| + |v n - L| := by
        simpa only [Real.dist_eq] using dist_triangle4
          (taggedSum q f α tag) (taggedSum q (F n) α tag) (v n) L
      _ < ε := by dsimp [D] at hδε; linarith

/-- Euclidean Stieltjes integration means integration of every real coordinate,
 with the same original integrator and endpoint convention. -/
def exercise17_hasVectorRSIntegral {k : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin k))
    (α : ℝ → ℝ) (a b : ℝ) (v : EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ j, HasRSIntegral (fun x => f x j) α a b (v j)

/-- Uniform limits commute with actual Euclidean vector Stieltjes integrals. -/
theorem exercise17_vector_integration {k : ℕ} {a b : ℝ} (hab : a ≤ b)
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b))
    {F : ℕ → ℝ → EuclideanSpace ℝ (Fin k)} {f : ℝ → EuclideanSpace ℝ (Fin k)}
    {v : ℕ → EuclideanSpace ℝ (Fin k)}
    (hF : ∀ n, exercise17_hasVectorRSIntegral (F n) α a b (v n))
    (hu : TendstoUniformlyOn F f atTop (Icc a b)) :
    ∃ L, exercise17_hasVectorRSIntegral f α a b L ∧ Tendsto v atTop (𝓝 L) := by
  have hj : ∀ j, TendstoUniformlyOn (fun n x => F n x j) (fun x => f x j)
      atTop (Icc a b) := by
    intro j
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn x hx
    apply lt_of_le_of_lt _ (hn x hx)
    simpa only [dist_eq_norm, Real.norm_eq_abs, PiLp.sub_apply] using
      PiLp.norm_apply_le (f x - F n x) j
  choose L hi hL using fun j => exercise17_stieltjes_uniform_limit hab hα
    (fun n => hF n j) (hj j)
  refine ⟨WithLp.toLp 2 L, hi, ?_⟩
  exact (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr hL)

/-- The mean-value estimate for differences of two genuine within derivatives. -/
private theorem exercise17_derivative_difference_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b C : ℝ}
    {u v du dv : ℝ → E}
    (hu : ∀ x ∈ Icc a b, HasDerivWithinAt u (du x) (Icc a b) x)
    (hv : ∀ x ∈ Icc a b, HasDerivWithinAt v (dv x) (Icc a b) x)
    (hb : ∀ x ∈ Icc a b, ‖du x - dv x‖ ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖(u y - v y) - (u x - v x)‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hu t ht).sub (hv t ht)) hb (convex_Icc a b) hx hy

/-- Derivative interchange on the entire closed interval in any real Banach space.
 All derivatives are genuine within derivatives, so both endpoints are included.
 No continuity of the derivatives or convergence away from `x₀` is assumed. -/
theorem exercise17_vector_differentiation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    {F D : ℕ → ℝ → E} {g : ℝ → E} {v : E}
    (hd : ∀ n x, x ∈ Icc a b → HasDerivWithinAt (F n) (D n x) (Icc a b) x)
    (hv : Tendsto (fun n => F n x₀) atTop (𝓝 v))
    (hD : TendstoUniformlyOn D g atTop (Icc a b)) :
    ∃ f : ℝ → E, TendstoUniformlyOn F f atTop (Icc a b) ∧
      ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x := by
  have hab : a ≤ b := hx₀.1.trans hx₀.2
  have hcD := Metric.uniformCauchySeqOn_iff.mp hD.uniformCauchySeqOn
  have hc : UniformCauchySeqOn F atTop (Icc a b) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    let δ := ε / (2 * (b - a + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ * (b - a) < ε / 2 := by
      have : δ * (2 * (b - a + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    obtain ⟨N₁, hN₁⟩ := hcD δ hδ
    obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun m hm n hn x hx => ?_⟩
    have he := exercise17_derivative_difference_bound (hd m) (hd n)
      (fun y hy => (show ‖D m y - D n y‖ < δ by
        simpa only [dist_eq_norm] using hN₁ m (le_trans (le_max_left _ _) hm)
          n (le_trans (le_max_left _ _) hn) y hy).le) hx₀ hx
    have hxbound : ‖x - x₀‖ ≤ b - a := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2, hx₀.1, hx₀.2]
    have he' : ‖(F m x - F n x) - (F m x₀ - F n x₀)‖ < ε / 2 :=
      he.trans_lt ((mul_le_mul_of_nonneg_left hxbound hδ.le).trans_lt hδε)
    have hv' : ‖F m x₀ - F n x₀‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hN₂ m (le_trans (le_max_right _ _) hm)
        n (le_trans (le_max_right _ _) hn)
    rw [dist_eq_norm]
    calc
      ‖F m x - F n x‖ ≤ ‖(F m x - F n x) - (F m x₀ - F n x₀)‖ +
          ‖F m x₀ - F n x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          ((F m x - F n x) - (F m x₀ - F n x₀)) (F m x₀ - F n x₀)
      _ < ε := by linarith
  have hcs : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x : Icc a b,
      dist (F m x) (F n x) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hc ε hε
    exact ⟨N, fun m hm n hn x => hN m hm n hn x x.property⟩
  obtain ⟨f₀, hf₀⟩ := (exercise17_complete_cauchy (fun n (x : Icc a b) => F n x)).mp hcs
  let f : ℝ → E := fun x => if hx : x ∈ Icc a b then f₀ ⟨x, hx⟩ else 0
  have hf : TendstoUniformlyOn F f atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hf₀ ε hε] with n hn x hx
    simpa only [f, dite_eq_left hx] using hn ⟨x, hx⟩
  refine ⟨f, hf, fun x hx => ?_⟩
  have hq : UniformCauchySeqOn (fun n => slope (F n) x) atTop (Icc a b \ {x}) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hcD (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have hyx : y ≠ x := by simpa only [mem_singleton_iff] using hy.2
    have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    have he := exercise17_derivative_difference_bound (hd m) (hd n)
      (fun z hz => (show ‖D m z - D n z‖ < ε / 2 by
        simpa only [dist_eq_norm] using hN m hm n hn z hz).le) hx hy.1
    rw [dist_eq_norm, slope_def_module, slope_def_module, ← smul_sub,
      norm_smul, norm_inv]
    apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
    rw [inv_mul_le_iff₀ hnorm, mul_comm]
    simpa only [sub_sub_sub_comm] using he
  have hqu : TendstoUniformlyOn (fun n => slope (F n) x) (slope f x)
      atTop (Icc a b \ {x}) := by
    apply hq.tendstoUniformlyOn_of_tendsto
    intro y hy
    simpa only [slope_def_module] using ((hf.tendsto_at hy.1).sub (hf.tendsto_at hx)).const_smul
      ((y - x)⁻¹ : ℝ)
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  exact (hqu.tendstoUniformlyOnFilter.mono_right inf_le_right).tendsto_of_eventually_tendsto
    (Eventually.of_forall (fun n => hasDerivWithinAt_iff_tendsto_slope.mp (hd n x hx)))
    (hD.tendsto_at hx)

end Rudin.Chapter07
