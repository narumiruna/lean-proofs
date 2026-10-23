module

public import Math.Rudin.Chapter07.Exercise19
public import Math.Rudin.Support.StieltjesComplex

@[expose] public section

open Set Filter
open scoped Topology NNReal
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
  Rudin.Support.StieltjesIntegralLaws Rudin.Support.StieltjesComplex
  Rudin.Support.StieltjesEquivalence

namespace Rudin.Chapter07

/-- The source Riemann integral has a bound without extra measurability assumptions. -/
theorem exercise18_complex_integral_bound {a b M : ℝ} {f : ℝ → ℂ} {z : ℂ}
    (hi : HasComplexRSIntegral f id a b z)
    (hb : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) : ‖z‖ ≤ 2 * M * (b - a) := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hi
  have hrb := hasRSIntegral_abs_le hr (fun t ht => (Complex.abs_re_le_norm (f t)).trans (hb t ht))
  have hib := hasRSIntegral_abs_le hi (fun t ht => (Complex.abs_im_le_norm (f t)).trans (hb t ht))
  have := Complex.norm_le_abs_re_add_abs_im z
  simp only [id_eq] at hrb hib
  linarith

/-- Indefinite Riemann integrals of a bounded function have a common Lipschitz bound. -/
theorem exercise18_primitive_lipschitz {a b : ℝ} {M : ℝ≥0} {f : ℝ → ℂ}
    {F : Icc a b → ℂ}
    (hi : ∀ x : Icc a b, HasComplexRSIntegral f id a x (F x))
    (hb : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) : LipschitzWith (2 * M) F := by
  have hle : ∀ x y : Icc a b, x ≤ y →
      dist (F x) (F y) ≤ (2 * M : ℝ≥0) * dist x y := by
    intro x y hxy
    change (x : ℝ) ≤ y at hxy
    obtain ⟨l, r, hl, hr, he⟩ := hasComplexRSIntegral_split x.property.1 hxy (hi y)
    have hlv : l = F x := hasComplexRSIntegral_unique hl (hi x)
    have hrb := exercise18_complex_integral_bound hr
      (fun t ht => hb t ⟨x.property.1.trans ht.1, ht.2.trans y.property.2⟩)
    have hv : r = F y - F x := by rw [hlv] at he; exact eq_sub_of_add_eq' he
    rw [hv] at hrb
    rw [dist_comm, dist_eq_norm]
    change ‖F y - F x‖ ≤ (2 * M : ℝ≥0) * |(x : ℝ) - y|
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, neg_sub] using hrb
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with h | h
  · exact hle x y h
  · simpa only [dist_comm] using hle y x h

/-- The primitive subsequence theorem for actual Riemann integral values.
Complex scalars include the real case. Both endpoints and singleton intervals are retained. -/
theorem exercise18_primitive_subsequence {a b : ℝ} (_hab : a ≤ b)
    {f : ℕ → ℝ → ℂ} {F : ℕ → Icc a b → ℂ} {M : ℝ≥0}
    (hi : ∀ n (x : Icc a b), HasComplexRSIntegral (f n) id a x (F n x))
    (hb : ∀ n t, t ∈ Icc a b → ‖f n t‖ ≤ M) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ G : C(Icc a b, ℂ),
      TendstoUniformly (fun n => F (k n)) G atTop := by
  classical
  have hl : ∀ n, LipschitzWith (2 * M) (F n) :=
    fun n => exercise18_primitive_lipschitz (hi n) (hb n)
  let P : ℕ → C(Icc a b, ℂ) := fun n => ⟨F n, (hl n).continuous⟩
  have he : Equicontinuous (fun p : range P => (p.val : Icc a b → ℂ)) := by
    have he' : Equicontinuous F := (LipschitzWith.uniformEquicontinuous F (2 * M) hl).equicontinuous
    have he'' := he'.comp (fun p : range P => p.property.choose)
    convert he'' using 1
    funext p x
    exact congrArg (fun q : C(Icc a b, ℂ) => q x) p.property.choose_spec.symm
  have hb' : ∀ x : Icc a b,
      Bornology.IsBounded ((fun p : C(Icc a b, ℂ) => p x) '' range P) := by
    intro x
    apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    refine ⟨2 * M * (b - a), ?_⟩
    rintro z ⟨p, ⟨n, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (exercise18_complex_integral_bound (hi n x)
      (fun t ht => hb n t ⟨ht.1, ht.2.trans x.property.2⟩)).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right x.property.2 a) (by positivity))
  obtain ⟨G, _, k, hk, hG⟩ := (exercise19_compact_closure hb' he).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨k, hk, G, ContinuousMap.tendsto_iff_tendstoUniformly.mp hG⟩

/-- Integrability on the full interval constructs all primitive values before selection. -/
theorem exercise18_exists_primitive_subsequence {a b : ℝ} (hab : a ≤ b)
    {f : ℕ → ℝ → ℂ} {M : ℝ≥0}
    (hi : ∀ n, ∃ z, HasComplexRSIntegral (f n) id a b z)
    (hb : ∀ n t, t ∈ Icc a b → ‖f n t‖ ≤ M) :
    ∃ F : ℕ → Icc a b → ℂ,
      (∀ n (x : Icc a b), HasComplexRSIntegral (f n) id a x (F n x)) ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ G : C(Icc a b, ℂ),
        TendstoUniformly (fun n => F (k n)) G atTop := by
  have h : ∀ n (x : Icc a b), ∃ z, HasComplexRSIntegral (f n) id a x z := by
    intro n x
    obtain ⟨z, hz⟩ := hi n
    obtain ⟨l, r, hl, _, _⟩ := hasComplexRSIntegral_split x.property.1 x.property.2 hz
    exact ⟨l, hl⟩
  choose F hF using h
  exact ⟨F, hF, exercise18_primitive_subsequence hab hF hb⟩

/-- Real Darboux-integrable functions satisfy the same source conclusion.
The passage through complex scalars is proved by the component bridge. -/
theorem exercise18_real_primitive_subsequence {a b : ℝ} (hab : a ≤ b)
    {f : ℕ → ℝ → ℝ} {M : ℝ≥0}
    (hi : ∀ n, ∃ z, HasDarbouxRSIntegral (f n) id a b z)
    (hb : ∀ n t, t ∈ Icc a b → |f n t| ≤ M) :
    ∃ F : ℕ → Icc a b → ℝ,
      (∀ n (x : Icc a b), HasDarbouxRSIntegral (f n) id a x (F n x)) ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ G : C(Icc a b, ℝ),
        TendstoUniformly (fun n => F (k n)) G atTop := by
  have hc : ∀ n, ∃ z, HasComplexRSIntegral (fun t => (f n t : ℂ)) id a b z := by
    intro n
    obtain ⟨z, hz⟩ := hi n
    refine ⟨(z : ℂ), hasComplexRSIntegral_iff.mpr ⟨?_, ?_⟩⟩
    · simpa using hasRSIntegral_of_hasDarbouxRSIntegral hab hz
    · simpa using hasRSIntegral_constant hab (monotone_id.monotoneOn (Icc a b)) 0
  obtain ⟨F, hF, k, hk, G, hG⟩ := exercise18_exists_primitive_subsequence hab hc
    (fun n t ht => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb n t ht)
  refine ⟨fun n x => (F n x).re, ?_, k, hk,
    ⟨fun x => (G x).re, Complex.continuous_re.comp G.continuous⟩, ?_⟩
  · intro n x
    exact hasDarbouxRSIntegral_of_hasRSIntegral x.property.1
      (by simpa using (hasComplexRSIntegral_iff.mp (hF n x)).1)
  · exact Complex.uniformContinuous_re.comp_tendstoUniformly hG

end Rudin.Chapter07
