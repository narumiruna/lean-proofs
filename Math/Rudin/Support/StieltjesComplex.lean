module

public import Math.Rudin.Support.StieltjesComposition
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex-valued literal Riemann–Stieltjes integrals

The definition uses actual complex tagged sums and norm convergence over the
same weak partitions. The component equivalence is proved, not used to assume
complex convergence. No measure or right normalization is introduced.
-/

@[expose] public section

noncomputable section

namespace Rudin.Support.StieltjesComplex

open Set Filter Topology StieltjesPrototype StieltjesRefinement StieltjesEquivalence
open StieltjesIntegralLaws StieltjesComposition

variable {a b : ℝ} {α : ℝ → ℝ} {f : ℝ → ℂ} {z : ℂ}

/-- Actual real-increment complex tagged sums. -/
def complexTaggedSum (p : Partition a b) (f : ℝ → ℂ) (α : ℝ → ℝ) (tag : ℕ → ℝ) : ℂ :=
  ∑ i ∈ Finset.range p.n, (α (p.x (i + 1)) - α (p.x i)) • f (tag i)

/-- Norm convergence of all tagged refinements, with source boundedness. -/
def HasComplexRSIntegral (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ) (z : ℂ) : Prop :=
  MonotoneOn α (Icc a b) ∧ (∃ M : ℝ, ∀ x ∈ Icc a b, ‖f x‖ ≤ M) ∧
    ∀ ε > (0 : ℝ), ∃ p : Partition a b, ∀ q : Partition a b, Refines q p →
      ∀ tag : ℕ → ℝ, IsTag q tag → ‖complexTaggedSum q f α tag - z‖ < ε

theorem complexTaggedSum_re (p : Partition a b) (f : ℝ → ℂ) (α : ℝ → ℝ) (tag : ℕ → ℝ) :
    (complexTaggedSum p f α tag).re = taggedSum p (fun x => (f x).re) α tag := by
  simp [complexTaggedSum, taggedSum, mul_comm]

theorem complexTaggedSum_im (p : Partition a b) (f : ℝ → ℂ) (α : ℝ → ℝ) (tag : ℕ → ℝ) :
    (complexTaggedSum p f α tag).im = taggedSum p (fun x => (f x).im) α tag := by
  simp [complexTaggedSum, taggedSum, mul_comm]

/-- The literal complex predicate is equivalent to the two real components. -/
theorem hasComplexRSIntegral_iff : HasComplexRSIntegral f α a b z ↔
    HasRSIntegral (fun x => (f x).re) α a b z.re ∧
    HasRSIntegral (fun x => (f x).im) α a b z.im := by
  constructor
  · intro hf
    obtain ⟨M, hM⟩ := hf.2.1
    constructor
    · refine ⟨hf.1, ⟨M, fun x hx => (Complex.abs_re_le_norm _).trans (hM x hx)⟩, ?_⟩
      intro ε hε
      obtain ⟨p, hp⟩ := hf.2.2 ε hε
      refine ⟨p, fun q hq tag ht => ?_⟩
      have h := Complex.abs_re_le_norm (complexTaggedSum q f α tag - z)
      rw [Complex.sub_re, complexTaggedSum_re] at h
      exact h.trans_lt (hp q hq tag ht)
    · refine ⟨hf.1, ⟨M, fun x hx => (Complex.abs_im_le_norm _).trans (hM x hx)⟩, ?_⟩
      intro ε hε
      obtain ⟨p, hp⟩ := hf.2.2 ε hε
      refine ⟨p, fun q hq tag ht => ?_⟩
      have h := Complex.abs_im_le_norm (complexTaggedSum q f α tag - z)
      rw [Complex.sub_im, complexTaggedSum_im] at h
      exact h.trans_lt (hp q hq tag ht)
  · rintro ⟨hr, hi⟩
    obtain ⟨M, hM⟩ := hr.2.1
    obtain ⟨N, hN⟩ := hi.2.1
    refine ⟨hr.1, ⟨M + N, ?_⟩, ?_⟩
    · intro x hx
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (hM x hx) (hN x hx))
    · intro ε hε
      obtain ⟨p, hp⟩ := common_control hr hi (ε := ε / 2) (δ := ε / 2)
        (by linarith) (by linarith)
      refine ⟨p, fun q hq tag ht => ?_⟩
      obtain ⟨h₁, h₂⟩ := hp q hq tag ht
      have h := Complex.norm_le_abs_re_add_abs_im (complexTaggedSum q f α tag - z)
      rw [Complex.sub_re, Complex.sub_im, complexTaggedSum_re, complexTaggedSum_im] at h
      linarith

theorem hasComplexRSIntegral_unique {w : ℂ}
    (hf : HasComplexRSIntegral f α a b z) (hg : HasComplexRSIntegral f α a b w) : z = w := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨kr, ki⟩ := hasComplexRSIntegral_iff.mp hg
  exact Complex.ext (hasRSIntegral_unique hr kr) (hasRSIntegral_unique hi ki)

theorem hasComplexRSIntegral_congr (hf : HasComplexRSIntegral f α a b z)
    {g : ℝ → ℂ} (hfg : ∀ x ∈ Icc a b, f x = g x) : HasComplexRSIntegral g α a b z := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  exact hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_congr hr (fun x hx => congrArg Complex.re (hfg x hx)),
      hasRSIntegral_congr hi (fun x hx => congrArg Complex.im (hfg x hx))⟩

/-- No complex integral-existence hypothesis is hidden in this closure law. -/
theorem exists_product (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b z)
    {g : ℝ → ℂ} {w : ℂ} (hg : HasComplexRSIntegral g α a b w) :
    ∃ value : ℂ, HasComplexRSIntegral (fun x => f x * g x) α a b value := by
  obtain ⟨fr, fi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨gr, gi⟩ := hasComplexRSIntegral_iff.mp hg
  obtain ⟨u, hu⟩ := exists_tagged_product hab fr gr
  obtain ⟨v, hv⟩ := exists_tagged_product hab fi gi
  obtain ⟨s, hs⟩ := exists_tagged_product hab fr gi
  obtain ⟨t, ht⟩ := exists_tagged_product hab fi gr
  refine ⟨⟨u - v, s + t⟩, hasComplexRSIntegral_iff.mpr ⟨?_, ?_⟩⟩
  · simpa only [Complex.mul_re] using hasRSIntegral_sub hu hv
  · simpa only [Complex.mul_im] using hasRSIntegral_add hs ht

/-- A finite complex tagged sum is bounded by the real tagged sum of norms. -/
theorem complexTaggedSum_norm_le (p : Partition a b) (f : ℝ → ℂ) (α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a b)) (tag : ℕ → ℝ) :
    ‖complexTaggedSum p f α tag‖ ≤ taggedSum p (fun x => ‖f x‖) α tag := by
  unfold complexTaggedSum taggedSum
  calc
    ‖∑ i ∈ Finset.range p.n, (α (p.x (i + 1)) - α (p.x i)) • f (tag i)‖ ≤
        ∑ i ∈ Finset.range p.n, ‖(α (p.x (i + 1)) - α (p.x i)) • f (tag i)‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Finset.range p.n, ‖f (tag i)‖ * (α (p.x (i + 1)) - α (p.x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (increment_nonneg p hα (Finset.mem_range.mp hi))]
      ring

/-- The norm of a complex integrand is genuinely integrable. -/
theorem exists_norm (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b z) :
    ∃ value : ℝ, HasRSIntegral (fun x => ‖f x‖) α a b value := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨r, hrr⟩ := exists_tagged_square hab hr
  obtain ⟨s, hss⟩ := exists_tagged_square hab hi
  have he (x : ℝ) : (f x).re ^ 2 + (f x).im ^ 2 = ‖f x‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hn : HasRSIntegral (fun x => ‖f x‖ ^ 2) α a b (r + s) :=
    hasRSIntegral_congr (hasRSIntegral_add hrr hss) (fun x _ => he x)
  obtain ⟨M, hM⟩ := hf.2.1
  have hRange : ∀ x ∈ Icc a b, ‖f x‖ ^ 2 ∈ Icc 0 (M ^ 2) := by
    intro x hx
    exact ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) (hM x hx) 2⟩
  obtain ⟨value, hv⟩ := exists_tagged_comp_continuous hab hn hRange
    Real.continuous_sqrt.continuousOn
  refine ⟨value, hasRSIntegral_congr hv ?_⟩
  intro x _
  simp

/-- The complex integral value is bounded by the real integral of its norm. -/
theorem integral_norm_le (hf : HasComplexRSIntegral f α a b z) {value : ℝ}
    (hg : HasRSIntegral (fun x => ‖f x‖) α a b value) : ‖z‖ ≤ value := by
  by_contra hn
  have hpos : 0 < ‖z‖ - value := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (‖z‖ - value) / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨p, hp⟩ := hf.2.2 ε hε
  obtain ⟨q, hq⟩ := hg.2.2 ε hε
  let r := commonRefinement p q
  have ht : IsTag r r.x := fun i hi => left_isTag r i hi
  have hc := hp r (commonRefinement_refines_left p q) r.x ht
  have hr := hq r (commonRefinement_refines_right p q) r.x ht
  have hb := complexTaggedSum_norm_le r f α hf.1 r.x
  have htri := norm_add_le (z - complexTaggedSum r f α r.x) (complexTaggedSum r f α r.x)
  rw [sub_add_cancel] at htri
  have hc' : ‖z - complexTaggedSum r f α r.x‖ < ε := by
    simpa only [norm_sub_rev] using hc
  have hr' := (abs_lt.mp hr).2
  dsimp only [ε] at hc' hr'
  linarith

theorem exists_norm_bound (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b z) :
    ∃ value : ℝ, HasRSIntegral (fun x => ‖f x‖) α a b value ∧ ‖z‖ ≤ value := by
  obtain ⟨value, hv⟩ := exists_norm hab hf
  exact ⟨value, hv, integral_norm_le hf hv⟩

theorem hasComplexRSIntegral_add (hf : HasComplexRSIntegral f α a b z)
    {g : ℝ → ℂ} {w : ℂ} (hg : HasComplexRSIntegral g α a b w) :
    HasComplexRSIntegral (fun x => f x + g x) α a b (z + w) := by
  obtain ⟨fr, fi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨gr, gi⟩ := hasComplexRSIntegral_iff.mp hg
  exact hasComplexRSIntegral_iff.mpr ⟨hasRSIntegral_add fr gr, hasRSIntegral_add fi gi⟩

/-- Multiplication by an arbitrary complex scalar is an actual integral law. -/
theorem hasComplexRSIntegral_mul (hf : HasComplexRSIntegral f α a b z) (c : ℂ) :
    HasComplexRSIntegral (fun x => c * f x) α a b (c * z) := by
  obtain ⟨fr, fi⟩ := hasComplexRSIntegral_iff.mp hf
  apply hasComplexRSIntegral_iff.mpr
  constructor
  · simpa only [Complex.mul_re] using
      hasRSIntegral_sub (hasRSIntegral_mul fr c.re) (hasRSIntegral_mul fi c.im)
  · simpa only [Complex.mul_im] using
      hasRSIntegral_add (hasRSIntegral_mul fi c.re) (hasRSIntegral_mul fr c.im)

theorem hasComplexRSIntegral_conj (hf : HasComplexRSIntegral f α a b z) :
    HasComplexRSIntegral (fun x => (starRingEnd ℂ) (f x)) α a b ((starRingEnd ℂ) z) := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  exact hasComplexRSIntegral_iff.mpr ⟨hr, hasRSIntegral_neg hi⟩

theorem hasComplexRSIntegral_constant (hab : a ≤ b)
    (hα : MonotoneOn α (Icc a b)) (c : ℂ) :
    HasComplexRSIntegral (fun _ => c) α a b ((α b - α a) • c) := by
  apply hasComplexRSIntegral_iff.mpr
  constructor
  · simpa [mul_comm] using hasRSIntegral_constant hab hα c.re
  · simpa [mul_comm] using hasRSIntegral_constant hab hα c.im

theorem hasComplexRSIntegral_neg (hf : HasComplexRSIntegral f α a b z) :
    HasComplexRSIntegral (fun x => -f x) α a b (-z) := by
  simpa only [neg_one_mul] using hasComplexRSIntegral_mul hf (-1)

theorem hasComplexRSIntegral_sub (hf : HasComplexRSIntegral f α a b z)
    {g : ℝ → ℂ} {w : ℂ} (hg : HasComplexRSIntegral g α a b w) :
    HasComplexRSIntegral (fun x => f x - g x) α a b (z - w) := by
  simpa only [sub_eq_add_neg] using hasComplexRSIntegral_add hf (hasComplexRSIntegral_neg hg)

theorem hasComplexRSIntegral_integrator_add (hf : HasComplexRSIntegral f α a b z)
    {β : ℝ → ℝ} {w : ℂ} (hg : HasComplexRSIntegral f β a b w) :
    HasComplexRSIntegral f (fun x => α x + β x) a b (z + w) := by
  obtain ⟨fr, fi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨gr, gi⟩ := hasComplexRSIntegral_iff.mp hg
  exact hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_integrator_add fr gr, hasRSIntegral_integrator_add fi gi⟩

theorem hasComplexRSIntegral_integrator_mul (hf : HasComplexRSIntegral f α a b z)
    {c : ℝ} (hc : 0 ≤ c) :
    HasComplexRSIntegral f (fun x => c * α x) a b (c • z) := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  apply hasComplexRSIntegral_iff.mpr
  constructor
  · simpa using hasRSIntegral_integrator_mul hr hc
  · simpa using hasRSIntegral_integrator_mul hi hc

theorem hasComplexRSIntegral_join {c : ℝ} {w : ℂ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : HasComplexRSIntegral f α a c z) (hg : HasComplexRSIntegral f α c b w) :
    HasComplexRSIntegral f α a b (z + w) := by
  obtain ⟨fr, fi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨gr, gi⟩ := hasComplexRSIntegral_iff.mp hg
  exact hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_join hac hcb fr gr, hasRSIntegral_join hac hcb fi gi⟩

/-- Restriction constructs both complex values, including endpoint cuts. -/
theorem hasComplexRSIntegral_split {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : HasComplexRSIntegral f α a b z) :
    ∃ left right : ℂ, HasComplexRSIntegral f α a c left ∧
      HasComplexRSIntegral f α c b right ∧ left + right = z := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨lr, rr, hlr, hrr, her⟩ := hasRSIntegral_split hac hcb hr
  obtain ⟨li, ri, hli, hri, hei⟩ := hasRSIntegral_split hac hcb hi
  refine ⟨⟨lr, li⟩, ⟨rr, ri⟩, hasComplexRSIntegral_iff.mpr ⟨hlr, hli⟩,
    hasComplexRSIntegral_iff.mpr ⟨hrr, hri⟩, ?_⟩
  exact Complex.ext her hei

end Rudin.Support.StieltjesComplex
