module

public import Math.Rudin.Support.StieltjesComplex
public import Math.Rudin.Chapter06.Exercise07
public import Mathlib.Analysis.MeanInequalities

/-!
# Chapter 6, Exercise 10

Source: Rudin, page 139 (PDF page 148), parts (a)–(d).
The proper integrals below use the original tagged sums for a raw monotone
integrator. In particular, no right-continuous normalization is made.
-/

@[expose] public section

noncomputable section

namespace Rudin.Chapter06

open Set Filter Topology
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
open Rudin.Support.StieltjesEquivalence Rudin.Support.StieltjesIntegralLaws
open Rudin.Support.StieltjesComposition Rudin.Support.StieltjesComplex

/-- The source assumptions are exactly positive conjugate exponents. -/
theorem conjugate_exponents {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / p + 1 / q = 1) : p.HolderConjugate q :=
  ⟨by simpa only [one_div, inv_one] using hpq, hp, hq⟩

/-- Exercise 10(a): Young's inequality, including either zero argument. -/
theorem young {p q u v : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / p + 1 / q = 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u * v ≤ u ^ p / p + v ^ q / q :=
  Real.young_inequality_of_nonneg hu hv (conjugate_exponents hp hq hpq)

/-- Exercise 10(a): the exact equality condition also covers `u = v = 0`. -/
theorem young_eq_iff {p q u v : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / p + 1 / q = 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u * v = u ^ p / p + v ^ q / q ↔ u ^ p = v ^ q :=
  Real.young_inequality_eq_iff_of_nonneg hu hv (conjugate_exponents hp hq hpq)

/-- Positive real powers of nonnegative raw-integrable functions exist. -/
theorem exists_rs_rpow {a b v p : ℝ} {f α : ℝ → ℝ} (hab : a ≤ b)
    (hf : HasRSIntegral f α a b v) (hp : 0 ≤ p)
    (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) :
    ∃ value : ℝ, HasRSIntegral (fun x => (f x) ^ p) α a b value := by
  obtain ⟨M, hM⟩ := hf.2.1
  exact exists_tagged_comp_continuous hab hf
    (fun x hx => ⟨hf₀ x hx, (le_abs_self _).trans (hM x hx)⟩)
    (Real.continuous_rpow_const hp).continuousOn

/-- Exercise 10(b): normalization and Young give the real integral bound.
The product integral is constructed from the two source integrands. -/
theorem holder_normalized {a b p q v w : ℝ} {f g α : ℝ → ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (hf : HasRSIntegral f α a b v) (hg : HasRSIntegral g α a b w)
    (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) (hg₀ : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hfp : HasRSIntegral (fun x => (f x) ^ p) α a b 1)
    (hgq : HasRSIntegral (fun x => (g x) ^ q) α a b 1) :
    ∃ value : ℝ, HasRSIntegral (fun x => f x * g x) α a b value ∧ value ≤ 1 := by
  obtain ⟨value, hv⟩ := exists_tagged_product hab hf hg
  refine ⟨value, hv, ?_⟩
  have hm := hasRSIntegral_mono hv
    (hasRSIntegral_add (hasRSIntegral_mul hfp (1 / p))
      (hasRSIntegral_mul hgq (1 / q))) (fun x hx => by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
          young hp hq hpq (hf₀ x hx) (hg₀ x hx))
  simpa only [mul_one, hpq] using hm

/-- Finite weighted Hölder uses the actual nonnegative increments, including
zero increments. No division by the total mass or either norm occurs. -/
theorem weighted_holder {ι : Type*} (s : Finset ι) {p q : ℝ}
    (hpq : p.HolderConjugate q) (f g w : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, f i * g i * w i) ≤
      (∑ i ∈ s, (f i) ^ p * w i) ^ (1 / p) *
      (∑ i ∈ s, (g i) ^ q * w i) ^ (1 / q) := by
  let F := fun i => f i * (w i) ^ (1 / p)
  let G := fun i => g i * (w i) ^ (1 / q)
  have hF (i) (hi : i ∈ s) : (F i) ^ p = (f i) ^ p * w i := by
    dsimp [F]
    rw [Real.mul_rpow (hf i hi) (Real.rpow_nonneg (hw i hi) _),
      ← Real.rpow_mul (hw i hi), one_div_mul_cancel hpq.ne_zero, Real.rpow_one]
  have hG (i) (hi : i ∈ s) : (G i) ^ q = (g i) ^ q * w i := by
    dsimp [G]
    rw [Real.mul_rpow (hg i hi) (Real.rpow_nonneg (hw i hi) _),
      ← Real.rpow_mul (hw i hi), one_div_mul_cancel hpq.symm.ne_zero, Real.rpow_one]
  have hFG (i) (hi : i ∈ s) : F i * G i = f i * g i * w i := by
    dsimp [F, G]
    calc
      _ = f i * g i * ((w i) ^ (1 / p) * (w i) ^ (1 / q)) := by ring
      _ = _ := by
        rw [← Real.rpow_add' (hw i hi) (by
          rw [one_div, one_div, hpq.inv_add_inv_eq_one]; norm_num),
          show 1 / p + 1 / q = 1 by simpa only [one_div] using hpq.inv_add_inv_eq_one,
          Real.rpow_one]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := F) (g := G) hpq
    (fun i hi => mul_nonneg (hf i hi) (Real.rpow_nonneg (hw i hi) _))
    (fun i hi => mul_nonneg (hg i hi) (Real.rpow_nonneg (hw i hi) _))
  rw [Finset.sum_congr rfl hFG, Finset.sum_congr rfl hF, Finset.sum_congr rfl hG] at h
  exact h

/-- Hölder passes directly from weighted tagged sums to their actual values.
Continuity of positive powers at zero includes both zero-norm cases. -/
theorem holder_real_values {a b p q A B C : ℝ} {f g α : ℝ → ℝ}
    (hpq : p.HolderConjugate q)
    (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) (hg₀ : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hA : HasRSIntegral (fun x => (f x) ^ p) α a b A)
    (hB : HasRSIntegral (fun x => (g x) ^ q) α a b B)
    (hC : HasRSIntegral (fun x => f x * g x) α a b C) :
    C ≤ A ^ (1 / p) * B ^ (1 / q) := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he (n) : 0 < e n := by dsimp [e]; positivity
  have hc (n : ℕ) : ∃ r : Partition a b,
      |taggedSum r (fun x => (f x) ^ p) α r.x - A| < e n ∧
      |taggedSum r (fun x => (g x) ^ q) α r.x - B| < e n ∧
      |taggedSum r (fun x => f x * g x) α r.x - C| < e n := by
    obtain ⟨s, hs⟩ := common_control hA hB (he n) (he n)
    obtain ⟨t, ht⟩ := hC.2.2 (e n) (he n)
    let r := commonRefinement s t
    obtain ⟨h₁, h₂⟩ := hs r (commonRefinement_refines_left s t) r.x (left_isTag r)
    exact ⟨r, h₁, h₂, ht r (commonRefinement_refines_right s t) r.x (left_isTag r)⟩
  choose r hr using hc
  have lim {u : ℕ → ℝ} {v : ℝ} (hu : ∀ n, |u n - v| < e n) :
      Tendsto u atTop (𝓝 v) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hu n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hAlim := lim (fun n => (hr n).1)
  have hBlim := lim (fun n => (hr n).2.1)
  have hClim := lim (fun n => (hr n).2.2)
  apply le_of_tendsto_of_tendsto' hClim
    (((Real.continuous_rpow_const hpq.one_div_nonneg).tendsto A).comp hAlim |>.mul
      (((Real.continuous_rpow_const hpq.symm.one_div_nonneg).tendsto B).comp hBlim))
  intro n
  exact weighted_holder (Finset.range (r n).n) hpq
    (fun i => f ((r n).x i)) (fun i => g ((r n).x i))
    (fun i => α ((r n).x (i + 1)) - α ((r n).x i))
    (fun i hi => hf₀ _ (node_mem (r n) (Finset.mem_range.mp hi).le))
    (fun i hi => hg₀ _ (node_mem (r n) (Finset.mem_range.mp hi).le))
    (fun i hi => increment_nonneg (r n) hA.1 (Finset.mem_range.mp hi))

/-- Norm powers are genuinely raw-integrable, not measure-integral notation. -/
theorem exists_complex_norm_rpow {a b p : ℝ} {f : ℝ → ℂ} {α : ℝ → ℝ} {z : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b z) (hp : 0 ≤ p) :
    ∃ value : ℝ, HasRSIntegral (fun x => ‖f x‖ ^ p) α a b value := by
  obtain ⟨v, hv⟩ := exists_norm hab hf
  exact exists_rs_rpow hab hv hp (fun _ _ => norm_nonneg _)

/-- Exercise 10(c), value form. Neither power integral is required to be positive. -/
theorem holder_complex_values {a b p q A B : ℝ} {f g : ℝ → ℂ}
    {α : ℝ → ℝ} {z : ℂ} (hpq : p.HolderConjugate q)
    (hA : HasRSIntegral (fun x => ‖f x‖ ^ p) α a b A)
    (hB : HasRSIntegral (fun x => ‖g x‖ ^ q) α a b B)
    (hfg : HasComplexRSIntegral (fun x => f x * g x) α a b z) :
    ‖z‖ ≤ A ^ (1 / p) * B ^ (1 / q) := by
  obtain ⟨r, _⟩ := hA.2.2 1 zero_lt_one
  obtain ⟨C, hC⟩ := exists_norm (endpoints_le r) hfg
  have hC' : HasRSIntegral (fun x => ‖f x‖ * ‖g x‖) α a b C := by
    simpa only [norm_mul] using hC
  exact (integral_norm_le hfg hC).trans
    (holder_real_values hpq (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hA hB hC')

/-- Exercise 10(c): product and power existence, together with complex Hölder.
This includes singleton intervals, raw jumps, zero mass, and zero power norms. -/
theorem holder_complex {a b p q : ℝ} {f g : ℝ → ℂ} {α : ℝ → ℝ} {v w : ℂ}
    (hab : a ≤ b) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (hf : HasComplexRSIntegral f α a b v) (hg : HasComplexRSIntegral g α a b w) :
    ∃ (A B : ℝ) (z : ℂ),
      HasRSIntegral (fun x => ‖f x‖ ^ p) α a b A ∧
      HasRSIntegral (fun x => ‖g x‖ ^ q) α a b B ∧
      HasComplexRSIntegral (fun x => f x * g x) α a b z ∧
      ‖z‖ ≤ A ^ (1 / p) * B ^ (1 / q) := by
  obtain ⟨A, hA⟩ := exists_complex_norm_rpow hab hf hp.le
  obtain ⟨B, hB⟩ := exists_complex_norm_rpow hab hg hq.le
  obtain ⟨z, hz⟩ := Rudin.Support.StieltjesComplex.exists_product hab hf hg
  exact ⟨A, B, z, hA, hB, hz,
    holder_complex_values (conjugate_exponents hp hq hpq) hA hB hz⟩

/-- The ordinary complex bridge is proved componentwise from the general
ordinary real bridge. It does not apply to an arbitrary Stieltjes integrator. -/
theorem complex_ordinary_integral {a b : ℝ} {f : ℝ → ℂ} {z : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f id a b z) :
    IntervalIntegrable f MeasureTheory.volume a b ∧
      (∫ x in a..b, f x) = z := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  have hR := Rudin.Support.RiemannIntegrability.intervalIntegrable_and_integral_eq hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hr)
  have hI := Rudin.Support.RiemannIntegrability.intervalIntegrable_and_integral_eq hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hi)
  have hfi : IntervalIntegrable f MeasureTheory.volume a b :=
    ⟨MeasureTheory.Integrable.re_im_iff.mp ⟨hR.1.1, hI.1.1⟩,
      MeasureTheory.Integrable.re_im_iff.mp ⟨hR.1.2, hI.1.2⟩⟩
  refine ⟨hfi, Complex.ext ?_ ?_⟩
  · exact (intervalIntegral.intervalIntegral_re hfi).symm.trans hR.2
  · exact (intervalIntegral.intervalIntegral_im hfi).symm.trans hI.2

/-- The product has both an actual proper Riemann integral and the same
ordinary complex interval-integral value. -/
theorem proper_complex_product {a b : ℝ} {f g : ℝ → ℂ} {v w : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f id a b v)
    (hg : HasComplexRSIntegral g id a b w) :
    HasComplexRSIntegral (fun x => f x * g x) id a b (∫ x in a..b, f x * g x) := by
  obtain ⟨z, hz⟩ := Rudin.Support.StieltjesComplex.exists_product hab hf hg
  rw [(complex_ordinary_integral hab hz).2]
  exact hz

/-- Young bounds every proper integral of the product norm. This bound is
used to prove existence, rather than assume an improper product integral. -/
theorem proper_product_norm_young {a b p q A B : ℝ} {f g : ℝ → ℂ} {z : ℂ}
    (hab : a ≤ b) (hpq : p.HolderConjugate q)
    (hA : HasRSIntegral (fun x => ‖f x‖ ^ p) id a b A)
    (hB : HasRSIntegral (fun x => ‖g x‖ ^ q) id a b B)
    (hfg : HasComplexRSIntegral (fun x => f x * g x) id a b z) :
    (∫ x in a..b, ‖f x * g x‖) ≤ A / p + B / q := by
  obtain ⟨N, hN⟩ := exists_norm hab hfg
  have hNvalue := Rudin.Support.RiemannIntegrability.intervalIntegrable_and_integral_eq hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hN)
  rw [hNvalue.2]
  have hbound := hasRSIntegral_mono hN
    (hasRSIntegral_add (hasRSIntegral_mul hA (1 / p)) (hasRSIntegral_mul hB (1 / q)))
    (fun x _ => by
      simpa only [norm_mul, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
        Real.young_inequality_of_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)) hpq)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hbound

/-- Exercise 10(d), infinite endpoint, for complex functions. Finite power
limits and local proper integrability imply existence of the product limit.
The proof first establishes absolute integrability from truncated Young bounds. -/
theorem holder_improper_top_complex {a p q A B : ℝ} {f g : ℝ → ℂ}
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (hf : ∀ b, a ≤ b → ∃ v, HasComplexRSIntegral f id a b v)
    (hg : ∀ b, a ≤ b → ∃ w, HasComplexRSIntegral g id a b w)
    (hA : HasImproperRiemannIntegralTop (fun x => ‖f x‖ ^ p) a A)
    (hB : HasImproperRiemannIntegralTop (fun x => ‖g x‖ ^ q) a B) :
    ∃ z : ℂ,
      (∀ b, a ≤ b → HasComplexRSIntegral (fun x => f x * g x) id a b
        (∫ x in a..b, f x * g x)) ∧
      Tendsto (fun b => ∫ x in a..b, f x * g x) atTop (𝓝 z) ∧
      ‖z‖ ≤ A ^ (1 / p) * B ^ (1 / q) := by
  have hc := conjugate_exponents hp hq hpq
  have hprod (b : ℝ) (hb : a ≤ b) : HasComplexRSIntegral (fun x => f x * g x) id a b
      (∫ x in a..b, f x * g x) := by
    obtain ⟨v, hv⟩ := hf b hb
    obtain ⟨w, hw⟩ := hg b hb
    exact proper_complex_product hb hv hw
  let cut : ℝ → ℝ := fun t => max a t
  have hcut : Tendsto cut atTop atTop :=
    tendsto_atTop_mono (fun _ => le_max_right _ _) tendsto_id
  have hYlim := ((hA.2.comp hcut).div_const p).add ((hB.2.comp hcut).div_const q)
  obtain ⟨M, hM⟩ := hYlim.isBoundedUnder_le
  have hi : MeasureTheory.IntegrableOn (fun x => f x * g x) (Ioi a) := by
    apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded M a
      (fun t => (complex_ordinary_integral (le_max_left a t)
        (hprod (cut t) (le_max_left a t))).1.1) hcut
    filter_upwards [hM] with t ht
    exact (proper_product_norm_young (le_max_left a t) hc
      (hasRSIntegral_of_hasDarbouxRSIntegral (le_max_left a t) (hA.1 (cut t) (le_max_left a t)))
      (hasRSIntegral_of_hasDarbouxRSIntegral (le_max_left a t) (hB.1 (cut t) (le_max_left a t)))
      (hprod (cut t) (le_max_left a t))).trans ht
  let z : ℂ := ∫ x in Ioi a, f x * g x
  have hz : Tendsto (fun b => ∫ x in a..b, f x * g x) atTop (𝓝 z) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hi tendsto_id
  refine ⟨z, hprod, hz, ?_⟩
  apply le_of_tendsto_of_tendsto hz.norm
    (((Real.continuous_rpow_const hc.one_div_nonneg).tendsto A).comp hA.2 |>.mul
      (((Real.continuous_rpow_const hc.symm.one_div_nonneg).tendsto B).comp hB.2))
  filter_upwards [eventually_ge_atTop a] with b hb
  exact holder_complex_values hc
    (hasRSIntegral_of_hasDarbouxRSIntegral hb (hA.1 b hb))
    (hasRSIntegral_of_hasDarbouxRSIntegral hb (hB.1 b hb)) (hprod b hb)

/-- Exercise 10(d), finite left endpoint, for complex functions. In particular
this covers the interval `(0,1]` in Exercise 7. Product convergence is a conclusion,
not an additional assumption. -/
theorem holder_improper_left_complex {a b p q A B : ℝ} {f g : ℝ → ℂ}
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (hf : ∀ c, a < c → c ≤ b → ∃ v, HasComplexRSIntegral f id c b v)
    (hg : ∀ c, a < c → c ≤ b → ∃ w, HasComplexRSIntegral g id c b w)
    (hA : HasImproperRiemannIntegralLeft (fun x => ‖f x‖ ^ p) a b A)
    (hB : HasImproperRiemannIntegralLeft (fun x => ‖g x‖ ^ q) a b B) :
    ∃ z : ℂ,
      (∀ c, a < c → c ≤ b → HasComplexRSIntegral (fun x => f x * g x) id c b
        (∫ x in c..b, f x * g x)) ∧
      Tendsto (fun c => ∫ x in c..b, f x * g x) (𝓝[>] a) (𝓝 z) ∧
      ‖z‖ ≤ A ^ (1 / p) * B ^ (1 / q) := by
  classical
  have hab := hA.1
  have hc := conjugate_exponents hp hq hpq
  have hprod (c : ℝ) (hca : a < c) (hcb : c ≤ b) :
      HasComplexRSIntegral (fun x => f x * g x) id c b (∫ x in c..b, f x * g x) := by
    obtain ⟨v, hv⟩ := hf c hca hcb
    obtain ⟨w, hw⟩ := hg c hca hcb
    exact proper_complex_product hcb hv hw
  let cut : ℝ → ℝ := fun t => if a < t ∧ t ≤ b then t else b
  have hcuta (t) : a < cut t := by dsimp [cut]; split_ifs with h; exact h.1; exact hab
  have hcutb (t) : cut t ≤ b := by dsimp [cut]; split_ifs with h; exact h.2; exact le_rfl
  have hcutEq : cut =ᶠ[𝓝[>] a] id := by
    filter_upwards [Ioc_mem_nhdsGT hab] with t ht
    exact ite_eq_left ht
  have hcut : Tendsto cut (𝓝[>] a) (𝓝 a) :=
    (tendsto_id.mono_right nhdsWithin_le_nhds).congr' hcutEq.symm
  have hYlim := (hA.2.2.div_const p).add (hB.2.2.div_const q)
  obtain ⟨M, hM⟩ := hYlim.isBoundedUnder_le
  have hi : MeasureTheory.IntegrableOn (fun x => f x * g x) (Ioc a b) := by
    apply MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
      (I := M) (a := cut) (l := 𝓝[>] a)
      (fun t => (complex_ordinary_integral (hcutb t) (hprod (cut t) (hcuta t) (hcutb t))).1.1)
      hcut
    filter_upwards [hM, Ioc_mem_nhdsGT hab] with t ht htab
    change (∫ x in Ioc (cut t) b, ‖f x * g x‖) ≤ M
    rw [show cut t = t from ite_eq_left htab, ← intervalIntegral.integral_of_le htab.2]
    exact (proper_product_norm_young htab.2 hc
      (hasRSIntegral_of_hasDarbouxRSIntegral htab.2 (hA.2.1 t htab.1 htab.2))
      (hasRSIntegral_of_hasDarbouxRSIntegral htab.2 (hB.2.1 t htab.1 htab.2))
      (hprod t htab.1 htab.2)).trans ht
  have hi' : MeasureTheory.IntegrableOn (fun x => f x * g x) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr hi)
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hi'
  rw [uIcc_of_le hab.le] at hcont
  have hz : Tendsto (fun c => ∫ x in c..b, f x * g x) (𝓝[>] a)
      (𝓝 (∫ x in a..b, f x * g x)) :=
    ((hcont a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hab)).tendsto
  refine ⟨_, hprod, hz, ?_⟩
  apply le_of_tendsto_of_tendsto hz.norm
    (((Real.continuous_rpow_const hc.one_div_nonneg).tendsto A).comp hA.2.2 |>.mul
      (((Real.continuous_rpow_const hc.symm.one_div_nonneg).tendsto B).comp hB.2.2))
  filter_upwards [Ioc_mem_nhdsGT hab] with c hcab
  exact holder_complex_values hc
    (hasRSIntegral_of_hasDarbouxRSIntegral hcab.2 (hA.2.1 c hcab.1 hcab.2))
    (hasRSIntegral_of_hasDarbouxRSIntegral hcab.2 (hB.2.1 c hcab.1 hcab.2))
    (hprod c hcab.1 hcab.2)

end Rudin.Chapter06
