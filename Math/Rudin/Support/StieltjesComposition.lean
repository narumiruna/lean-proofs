module

public import Math.Rudin.Support.StieltjesIntegralLaws
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Composition and products for literal real Stieltjes integrals

The proofs control closed-cell oscillations and construct an integral from
small Darboux gaps. They do not replace the raw integrator by a measure.
Source: Rudin Theorems 6.11 and 6.13(a), book pages 127–129.
-/

@[expose] public section

namespace Rudin.Support.StieltjesComposition

open Set Filter Topology StieltjesPrototype StieltjesRefinement StieltjesEquivalence
open StieltjesIntegralLaws

variable {a b v : ℝ} {f α φ : ℝ → ℝ}

/-- An affine oscillation modulus gives an actual Darboux-gap bound. -/
theorem composition_gap_le (p : Partition a b) (hα : MonotoneOn α (Icc a b))
    {M η K : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (hK : 0 ≤ K)
    (hφ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |φ (f x) - φ (f y)| ≤ η + K * |f x - f y|) :
    upperSum p (φ ∘ f) α - lowerSum p (φ ∘ f) α ≤
      η * (α b - α a) + K * (upperSum p f α - lowerSum p f α) := by
  have hc (i : ℕ) (hi : i < p.n) :
      sSup ((φ ∘ f) '' Icc (p.x i) (p.x (i + 1))) -
          sInf ((φ ∘ f) '' Icc (p.x i) (p.x (i + 1))) ≤
        η + K * (sSup (f '' Icc (p.x i) (p.x (i + 1))) -
          sInf (f '' Icc (p.x i) (p.x (i + 1)))) := by
    let s := Icc (p.x i) (p.x (i + 1))
    have hs : s.Nonempty := ⟨p.x i, left_isTag p i hi⟩
    have hb : BddBelow (f '' s) := by
      refine ⟨-M, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hM x (cell_subset p hi hx))).1
    have ha : BddAbove (f '' s) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hM x (cell_subset p hi hx))).2
    have hosc (x : ℝ) (hx : x ∈ s) (y : ℝ) (hy : y ∈ s) :
        φ (f x) - φ (f y) ≤ η + K * (sSup (f '' s) - sInf (f '' s)) := by
      have hxl := csInf_le hb (mem_image_of_mem f hx)
      have hyl := csInf_le hb (mem_image_of_mem f hy)
      have hxu := le_csSup ha (mem_image_of_mem f hx)
      have hyu := le_csSup ha (mem_image_of_mem f hy)
      have hd : |f x - f y| ≤ sSup (f '' s) - sInf (f '' s) := by
        apply abs_le.mpr
        constructor <;> linarith
      have hp := hφ x (cell_subset p hi hx) y (cell_subset p hi hy)
      have hk := mul_le_mul_of_nonneg_left hd hK
      linarith [le_abs_self (φ (f x) - φ (f y))]
    rw [sub_le_iff_le_add]
    apply csSup_le (hs.image _)
    rintro _ ⟨x, hx, rfl⟩
    have hl : φ (f x) - (η + K * (sSup (f '' s) - sInf (f '' s))) ≤
        sInf ((φ ∘ f) '' s) := by
      apply le_csInf (hs.image _)
      rintro _ ⟨y, hy, rfl⟩
      change φ (f x) - (η + K * (sSup (f '' s) - sInf (f '' s))) ≤ φ (f y)
      linarith [hosc x hx y hy]
    change φ (f x) ≤ η + K * (sSup (f '' s) - sInf (f '' s)) + sInf ((φ ∘ f) '' s)
    linarith
  have ht : (∑ i ∈ Finset.range p.n, η * (α (p.x (i + 1)) - α (p.x i))) =
      η * (α b - α a) := taggedSum_const p α η p.x
  calc
    upperSum p (φ ∘ f) α - lowerSum p (φ ∘ f) α =
        ∑ i ∈ Finset.range p.n,
          (sSup ((φ ∘ f) '' Icc (p.x i) (p.x (i + 1))) -
            sInf ((φ ∘ f) '' Icc (p.x i) (p.x (i + 1)))) *
              (α (p.x (i + 1)) - α (p.x i)) := by
      unfold upperSum lowerSum
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ Finset.range p.n,
        (η + K * (sSup (f '' Icc (p.x i) (p.x (i + 1))) -
          sInf (f '' Icc (p.x i) (p.x (i + 1))))) *
            (α (p.x (i + 1)) - α (p.x i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hc i (Finset.mem_range.mp hi))
        (increment_nonneg p hα (Finset.mem_range.mp hi))
    _ = η * (α b - α a) + K * (upperSum p f α - lowerSum p f α) := by
      rw [← ht]
      unfold upperSum lowerSum
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Lipschitz control on the actual bounded range preserves integrability. -/
theorem exists_comp_lipschitz (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v)
    {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |φ (f x) - φ (f y)| ≤ K * |f x - f y|) :
    ∃ value : ℝ, HasDarbouxRSIntegral (φ ∘ f) α a b value := by
  obtain ⟨M, hM⟩ := hf.2.1
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : ∀ x ∈ Icc a b, |φ (f x)| ≤ |φ (f a)| + K * (2 * M) := by
    intro x hx
    have hd : |f x - f a| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [hM x hx, hM a ha])
    calc
      |φ (f x)| ≤ |φ (f x) - φ (f a)| + |φ (f a)| := by
        linarith [abs_sub_abs_le_abs_sub (φ (f x)) (φ (f a))]
      _ ≤ K * |f x - f a| + |φ (f a)| := by linarith [hφ x hx a ha]
      _ ≤ |φ (f a)| + K * (2 * M) := by
        have := mul_le_mul_of_nonneg_left hd hK
        linarith
  apply exists_hasDarbouxRSIntegral_of_small_gap hab hf.1 hb
  intro ε hε
  obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf)
    (show 0 < (ε / (K + 1)) / 2 by positivity)
  have hg : upperSum p f α - lowerSum p f α < ε / (K + 1) := by
    linarith
  have hgap := lowerSum_le_upperSum p hf.1 hM
  refine ⟨p, ?_⟩
  calc
    upperSum p (φ ∘ f) α - lowerSum p (φ ∘ f) α ≤
        K * (upperSum p f α - lowerSum p f α) := by
      simpa using composition_gap_le p hf.1 hM hK
        (show ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
          |φ (f x) - φ (f y)| ≤ 0 + K * |f x - f y| by simpa using hφ)
    _ ≤ (K + 1) * (upperSum p f α - lowerSum p f α) := by nlinarith
    _ < ε := by
      have hh := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hg
      nlinarith

/-- Rudin's continuous-composition theorem, on a closed interval containing
all integrand values. Continuity of the original integrand is not assumed. -/
theorem exists_comp_continuous (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v)
    {m M : ℝ} (hrange : ∀ x ∈ Icc a b, f x ∈ Icc m M)
    (hφ : ContinuousOn φ (Icc m M)) :
    ∃ value : ℝ, HasDarbouxRSIntegral (φ ∘ f) α a b value := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hφ.abs
  let B := |C|
  have hB : ∀ x ∈ Icc a b, |φ (f x)| ≤ B := by
    intro x hx
    exact (hC (mem_image_of_mem _ (hrange x hx))).trans (le_abs_self C)
  obtain ⟨F, hF⟩ := hf.2.1
  apply exists_hasDarbouxRSIntegral_of_small_gap hab hf.1 hB
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hf.1 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let η := (ε / 2) / (A + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηA : η * A < ε / 2 := by
    have he : η * (A + 1) = ε / 2 := by
      dsimp only [η]
      exact div_mul_cancel₀ _ (by linarith)
    nlinarith
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) η hη
  let K := (2 * B) / δ
  have hK : 0 ≤ K := by dsimp [K, B]; positivity
  have hmod : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |φ (f x) - φ (f y)| ≤ η + K * |f x - f y| := by
    intro x hx y hy
    by_cases hd : |f x - f y| < δ
    · have hh := hu (f x) (hrange x hx) (f y) (hrange y hy)
        (by simpa only [Real.dist_eq] using hd)
      have hh' : |φ (f x) - φ (f y)| < η := by simpa only [Real.dist_eq] using hh
      have hp := mul_nonneg hK (abs_nonneg (f x - f y))
      linarith
    · have hd' : δ ≤ |f x - f y| := le_of_not_gt hd
      have hl : 2 * B ≤ K * |f x - f y| := by
        calc
          2 * B = K * δ := (div_mul_cancel₀ _ hδ.ne').symm
          _ ≤ K * |f x - f y| := mul_le_mul_of_nonneg_left hd' hK
      have hh : |φ (f x) - φ (f y)| ≤ 2 * B :=
        (abs_sub _ _).trans (by linarith [hB x hx, hB y hy])
      linarith
  obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf)
    (show 0 < ((ε / 2) / (K + 1)) / 2 by positivity)
  have hg : upperSum p f α - lowerSum p f α < (ε / 2) / (K + 1) := by linarith
  have hg0 := lowerSum_le_upperSum p hf.1 hF
  have hKg : K * (upperSum p f α - lowerSum p f α) < ε / 2 := by
    have hh := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hg
    nlinarith
  refine ⟨p, ?_⟩
  exact (composition_gap_le p hf.1 hF hK hmod).trans_lt (by change η * A + _ < ε; linarith)

/-- Squaring an integrand preserves its literal Darboux integrability. -/
theorem exists_square (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ value : ℝ, HasDarbouxRSIntegral (fun x => (f x) ^ 2) α a b value := by
  obtain ⟨M, hM⟩ := hf.2.1
  have hrange : ∀ x ∈ Icc a b, f x ∈ Icc (-M) M := by
    intro x hx
    exact abs_le.mp (hM x hx)
  exact exists_comp_continuous hab hf hrange (continuous_id.pow 2).continuousOn

/-- Products exist without continuity of either integrand. The proof uses
polarization and the proved square and linearity laws, not a product integral. -/
theorem exists_product (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v)
    {g : ℝ → ℝ} {w : ℝ} (hg : HasDarbouxRSIntegral g α a b w) :
    ∃ value : ℝ, HasDarbouxRSIntegral (fun x => f x * g x) α a b value := by
  obtain ⟨u, hu⟩ := exists_square hab (hasDarbouxRSIntegral_add hab hf hg)
  obtain ⟨s, hs⟩ := exists_square hab hf
  obtain ⟨t, ht⟩ := exists_square hab hg
  have hh := hasDarbouxRSIntegral_mul hab
    (hasDarbouxRSIntegral_sub hab (hasDarbouxRSIntegral_sub hab hu hs) ht) (1 / 2)
  exact ⟨_, hasDarbouxRSIntegral_congr hab hh (by intro x _; ring)⟩

/-- All natural powers, including the zeroth power on singleton intervals. -/
theorem exists_power (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) (n : ℕ) :
    ∃ value : ℝ, HasDarbouxRSIntegral (fun x => (f x) ^ n) α a b value := by
  obtain ⟨M, hM⟩ := hf.2.1
  have hrange : ∀ x ∈ Icc a b, f x ∈ Icc (-M) M :=
    fun x hx => abs_le.mp (hM x hx)
  exact exists_comp_continuous hab hf hrange (continuous_id.pow n).continuousOn

/-- Tagged versions use the proved equivalence, not a new integration convention. -/
theorem exists_tagged_comp_continuous (hab : a ≤ b) (hf : HasRSIntegral f α a b v)
    {m M : ℝ} (hrange : ∀ x ∈ Icc a b, f x ∈ Icc m M)
    (hφ : ContinuousOn φ (Icc m M)) :
    ∃ value : ℝ, HasRSIntegral (φ ∘ f) α a b value := by
  obtain ⟨value, hv⟩ := exists_comp_continuous hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hf) hrange hφ
  exact ⟨value, hasRSIntegral_of_hasDarbouxRSIntegral hab hv⟩

theorem exists_tagged_square (hab : a ≤ b) (hf : HasRSIntegral f α a b v) :
    ∃ value : ℝ, HasRSIntegral (fun x => (f x) ^ 2) α a b value := by
  obtain ⟨value, hv⟩ := exists_square hab (hasDarbouxRSIntegral_of_hasRSIntegral hab hf)
  exact ⟨value, hasRSIntegral_of_hasDarbouxRSIntegral hab hv⟩

theorem exists_tagged_product (hab : a ≤ b) (hf : HasRSIntegral f α a b v)
    {g : ℝ → ℝ} {w : ℝ} (hg : HasRSIntegral g α a b w) :
    ∃ value : ℝ, HasRSIntegral (fun x => f x * g x) α a b value := by
  obtain ⟨value, hv⟩ := exists_product hab (hasDarbouxRSIntegral_of_hasRSIntegral hab hf)
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hg)
  exact ⟨value, hasRSIntegral_of_hasDarbouxRSIntegral hab hv⟩

theorem exists_tagged_power (hab : a ≤ b) (hf : HasRSIntegral f α a b v) (n : ℕ) :
    ∃ value : ℝ, HasRSIntegral (fun x => (f x) ^ n) α a b value := by
  obtain ⟨value, hv⟩ := exists_power hab (hasDarbouxRSIntegral_of_hasRSIntegral hab hf) n
  exact ⟨value, hasRSIntegral_of_hasDarbouxRSIntegral hab hv⟩

end Rudin.Support.StieltjesComposition
