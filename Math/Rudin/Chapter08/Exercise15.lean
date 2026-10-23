module

public import Math.Rudin.Chapter08.Exercise11
public import Math.Rudin.Support.RiemannAffine
public import Mathlib.Analysis.Fourier.AddCircle

/-! # Chapter 8, Exercise 15
Source Fourier conventions, genuine Dirichlet and Fejer kernels, arithmetic Fourier
means, convolution and uniform convergence. Source: book page 199, PDF page 208. -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Rudin.Chapter08

/-- The source Fourier monomial. -/
def fourierMonomial (n : ℤ) (x : ℝ) : ℂ := Complex.exp (Complex.I * n * x)

/-- The source Fourier coefficient on any interval of length `2π`. -/
def fourierCoefficient (a : ℝ) (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ x in a..a + 2 * Real.pi, fourierMonomial (-n) x * f x

theorem fourierMonomial_bridge (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 * Real.pi)) = fourierMonomial n x := by
  rw [fourier_coe_apply, fourierMonomial]
  congr 1
  push_cast
  field_simp

/-- Both the frequency and the Haar mass are converted to the source convention. -/
theorem fourierCoefficient_bridge (a : ℝ) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (show a < a + 2 * Real.pi by linarith [Real.pi_pos]) f n =
      fourierCoefficient a f n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [add_sub_cancel_left]
  unfold fourierCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  congr 1
  rw [fourier_coe_apply, fourierMonomial]
  congr 1
  push_cast
  field_simp
  <;> ring

/-- Parseval in the source convention, on functions rather than `Lp` classes. -/
theorem source_parseval (a : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc a (a + 2 * Real.pi)))) :
    HasSum (fun n : ℤ => ‖fourierCoefficient a f n‖ ^ 2)
      ((1 / (2 * Real.pi)) * ∫ x in a..a + 2 * Real.pi, ‖f x‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn
    (show a < a + 2 * Real.pi by linarith [Real.pi_pos]) hf
  simpa only [fourierCoefficient_bridge, add_sub_cancel_left, one_div, smul_eq_mul] using h

/-- The real form of the symmetric Dirichlet kernel. -/
def dirichletKernel (n : ℕ) (x : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range n, Real.cos (((k + 1 : ℕ) : ℝ) * x)

/-- Fejer's kernel is defined by the mean, including at removable singularities. -/
def fejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1), dirichletKernel n x) / (N + 1 : ℝ)

lemma dirichletKernel_succ (n : ℕ) (x : ℝ) :
    dirichletKernel (n + 1) x = dirichletKernel n x + 2 * Real.cos (((n + 1 : ℕ) : ℝ) * x) := by
  simp only [dirichletKernel, Finset.sum_range_succ]
  ring

lemma dirichletKernel_telescope (n : ℕ) (x : ℝ) :
    (1 - Real.cos x) * dirichletKernel n x =
      Real.cos ((n : ℝ) * x) - Real.cos (((n + 1 : ℕ) : ℝ) * x) := by
  induction n with
  | zero => simp [dirichletKernel]
  | succ n ih =>
    rw [dirichletKernel_succ, mul_add, ih]
    have h := Real.cos_add (((n + 1 : ℕ) : ℝ) * x) x
    have h' := Real.cos_sub (((n + 1 : ℕ) : ℝ) * x) x
    have e1 : ((n + 1 : ℕ) : ℝ) * x + x = ((n + 1 + 1 : ℕ) : ℝ) * x := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℝ) * x - x = (n : ℝ) * x := by push_cast; ring
    rw [e1] at h
    rw [e2] at h'
    nlinarith

lemma fejerKernel_telescope (N : ℕ) (x : ℝ) :
    (1 - Real.cos x) * fejerKernel N x =
      (1 - Real.cos (((N + 1 : ℕ) : ℝ) * x)) / (N + 1 : ℝ) := by
  unfold fejerKernel
  rw [← mul_div_assoc, Finset.mul_sum]
  simp_rw [dirichletKernel_telescope]
  rw [Finset.sum_range_sub']
  simp

theorem exercise15_kernel_formula (N : ℕ) {x : ℝ}
    (hx : ∀ k : ℤ, x ≠ k * (2 * Real.pi)) :
    fejerKernel N x = (1 - Real.cos (((N + 1 : ℕ) : ℝ) * x)) /
      ((N + 1 : ℝ) * (1 - Real.cos x)) := by
  have hne : 1 - Real.cos x ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff x).mp (by linarith)
    exact hx k hk.symm
  apply (eq_div_iff (mul_ne_zero (by positivity) hne)).mpr
  have h := fejerKernel_telescope N x
  field_simp at h
  nlinarith [h]

theorem exercise15_continuous (N : ℕ) : Continuous (fejerKernel N) := by
  unfold fejerKernel dirichletKernel
  fun_prop

theorem exercise15_kernel_at_multiple (N : ℕ) (k : ℤ) :
    fejerKernel N (k * (2 * Real.pi)) = N + 1 := by
  have hc (n : ℕ) : Real.cos ((n : ℝ) * (k * (2 * Real.pi))) = 1 := by
    have he : (n : ℝ) * (k * (2 * Real.pi)) = ((n : ℤ) * k : ℤ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [he, Real.cos_int_mul_two_pi]
  have hd (n : ℕ) : dirichletKernel n (k * (2 * Real.pi)) = 2 * n + 1 := by
    unfold dirichletKernel
    simp_rw [hc]
    simp
    ring
  unfold fejerKernel
  simp_rw [hd]
  have hs (m : ℕ) : (∑ n ∈ Finset.range m, (2 * (n : ℝ) + 1)) = (m : ℝ) ^ 2 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [hs]
  push_cast
  field_simp

theorem exercise15_nonnegative (N : ℕ) (x : ℝ) : 0 ≤ fejerKernel N x := by
  by_cases h : ∃ k : ℤ, x = k * (2 * Real.pi)
  · obtain ⟨k, rfl⟩ := h
    rw [exercise15_kernel_at_multiple]
    positivity
  · rw [exercise15_kernel_formula N (by simpa only [not_exists] using h)]
    apply div_nonneg
    · linarith [Real.cos_le_one (((N + 1 : ℕ) : ℝ) * x)]
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one x))

lemma dirichletKernel_integral (n : ℕ) :
    (∫ x in -Real.pi..Real.pi, dirichletKernel n x) = 2 * Real.pi := by
  have hc (k : ℕ) : (∫ x in -Real.pi..Real.pi,
      Real.cos (((k + 1 : ℕ) : ℝ) * x)) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left Real.cos (by positivity), integral_cos]
    simp only [mul_neg, Real.sin_neg, Real.sin_nat_mul_pi, neg_zero, sub_zero, smul_zero]
  unfold dirichletKernel
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [hc, Finset.sum_const_zero, mul_zero, add_zero, intervalIntegral.integral_const,
    sub_neg_eq_add, smul_eq_mul, mul_one]
  ring

theorem exercise15_mass (N : ℕ) :
    (1 / (2 * Real.pi)) * (∫ x in -Real.pi..Real.pi, fejerKernel N x) = 1 := by
  unfold fejerKernel
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum (fun n _ => by
      apply Continuous.intervalIntegrable
      unfold dirichletKernel
      fun_prop)]
  simp only [dirichletKernel_integral, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem exercise15_off_zero_bound (N : ℕ) {δ x : ℝ}
    (hδ : 0 < δ) (hdx : δ ≤ |x|) (hx : |x| ≤ Real.pi) :
    fejerKernel N x ≤ 2 / ((N + 1 : ℝ) * (1 - Real.cos δ)) := by
  have hdπ : δ ≤ Real.pi := hdx.trans hx
  have hcd : Real.cos δ < 1 := by
    have h := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hδ.le, hdπ⟩ hδ
    simpa using h
  have hcx : Real.cos x ≤ Real.cos δ := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi hδ.le hx hdx
  have hd : 0 < 1 - Real.cos δ := by linarith
  have hp : 0 < (N + 1 : ℝ) := by positivity
  have he : ∀ k : ℤ, x ≠ k * (2 * Real.pi) := by
    intro k hk
    rw [hk, Real.cos_int_mul_two_pi] at hcx
    linarith
  rw [exercise15_kernel_formula N he]
  calc
    _ ≤ 2 / ((N + 1 : ℝ) * (1 - Real.cos x)) := by
      apply div_le_div_of_nonneg_right
      · linarith [Real.neg_one_le_cos (((N + 1 : ℕ) : ℝ) * x)]
      · exact mul_nonneg hp.le (sub_nonneg.mpr (Real.cos_le_one x))
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (mul_pos hp hd)
      (mul_le_mul_of_nonneg_left (by linarith) hp.le)

lemma fourierMonomial_trig (n : ℤ) (x : ℝ) :
    fourierMonomial n x = (Real.cos ((n : ℝ) * x) : ℂ) +
      (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I := by
  unfold fourierMonomial
  rw [show Complex.I * n * x = ((n : ℝ) * x : ℝ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  simp

lemma fourierMonomial_periodic (n : ℤ) : Function.Periodic (fourierMonomial n) (2 * Real.pi) := by
  intro x
  rw [← fourierMonomial_bridge, ← fourierMonomial_bridge]
  congr 1
  simp

lemma fourierMonomial_sub (n : ℤ) (x t : ℝ) :
    fourierMonomial n (x - t) = fourierMonomial n x * fourierMonomial (-n) t := by
  simp only [fourierMonomial, Complex.ofReal_sub, Int.cast_neg]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- A single Fourier mode has the source convolution normalization. -/
lemma fourier_mode_convolution {f : ℝ → ℂ} (hf : Function.Periodic f (2 * Real.pi))
    (n : ℤ) (x : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, fourierMonomial n t * f (x - t)) =
      fourierCoefficient (-Real.pi) f n * fourierMonomial n x := by
  have hp : Function.Periodic (fun u => fourierMonomial (-n) u * f u) (2 * Real.pi) :=
    (fourierMonomial_periodic (-n)).mul hf
  have he : (∫ t in -Real.pi..Real.pi, fourierMonomial n t * f (x - t)) =
      fourierMonomial n x * ∫ t in -Real.pi..Real.pi,
        fourierMonomial (-n) (x - t) * f (x - t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have hm := fourierMonomial_sub n x (x - t)
    rw [sub_sub_cancel] at hm
    dsimp only
    rw [← mul_assoc, ← hm]
  rw [he, intervalIntegral.integral_comp_sub_left
    (fun u => fourierMonomial (-n) u * f u)]
  have hb : x - -Real.pi = (x - Real.pi) + 2 * Real.pi := by ring
  rw [hb, hp.intervalIntegral_add_eq (x - Real.pi) (-Real.pi)]
  simp only [fourierCoefficient, Complex.real_smul]
  ring

/-- The symmetric Fourier sum, grouped as the zero mode and positive/negative pairs. -/
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  fourierCoefficient (-Real.pi) f 0 + ∑ k ∈ Finset.range N,
    (fourierCoefficient (-Real.pi) f (k + 1) * fourierMonomial (k + 1) x +
      fourierCoefficient (-Real.pi) f (-(k + 1)) * fourierMonomial (-(k + 1)) x)

/-- The arithmetic means of the actual symmetric Fourier partial sums. -/
def fejerMean (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (1 / (N + 1 : ℝ)) • ∑ n ∈ Finset.range (N + 1), fourierPartialSum f n x

lemma dirichletKernel_complex (N : ℕ) (x : ℝ) :
    (dirichletKernel N x : ℂ) = 1 + ∑ k ∈ Finset.range N,
      (fourierMonomial (k + 1) x + fourierMonomial (-(k + 1)) x) := by
  simp only [dirichletKernel, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_sum]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourierMonomial_trig, fourierMonomial_trig]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
  ring

lemma periodic_riemann_intervalIntegrable {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  obtain ⟨z, hz⟩ := hf
  have hi := (complex_riemann_bridge (by linarith [Real.pi_pos]) hz).1
  apply hp.intervalIntegrable (t := -Real.pi) (by positivity) _ a b
  convert hi using 1 <;> ring

lemma periodic_riemann_reflected {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (x : ℝ) :
    IntervalIntegrable (fun t => f (x - t)) volume (-Real.pi) Real.pi := by
  convert (periodic_riemann_intervalIntegrable hp hf (x + Real.pi) (x - Real.pi)).comp_sub_left x
    using 1 <;> ring

lemma fourierPartialSum_convolution {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, (dirichletKernel N t : ℂ) * f (x - t)) := by
  have hi := periodic_riemann_reflected hp hf x
  have hm (n : ℤ) : IntervalIntegrable
      (fun t => fourierMonomial n t * f (x - t)) volume (-Real.pi) Real.pi :=
    hi.continuousOn_mul (by unfold fourierMonomial; fun_prop)
  simp_rw [dirichletKernel_complex, add_mul, one_mul, Finset.sum_mul, add_mul]
  have hs : IntervalIntegrable (fun t => ∑ k ∈ Finset.range N,
      (fourierMonomial (k + 1) t * f (x - t) + fourierMonomial (-(k + 1)) t * f (x - t)))
      volume (-Real.pi) Real.pi := by
    convert IntervalIntegrable.sum (Finset.range N)
      (fun k _ => (hm (k + 1)).add (hm (-(k + 1)))) using 1
    ext t
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_add hi hs,
    intervalIntegral.integral_finsetSum (s := Finset.range N)
      (fun (k : ℕ) _ => (hm (k + 1)).add (hm (-(k + 1))))]
  simp_rw [intervalIntegral.integral_add (hm _) (hm _)]
  simp only [smul_add, Finset.smul_sum]
  simp_rw [fourier_mode_convolution hp]
  unfold fourierPartialSum
  congr 1
  have h := fourier_mode_convolution hp 0 x
  simpa [fourierMonomial] using h.symm

/-- The source convolution formula for arithmetic means of Fourier sums. -/
theorem exercise15_convolution {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    fejerMean f N x = (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, fejerKernel N t • f (x - t)) := by
  have hi := periodic_riemann_reflected hp hf x
  have hd (n : ℕ) : IntervalIntegrable
      (fun t => (dirichletKernel n t : ℂ) * f (x - t)) volume (-Real.pi) Real.pi :=
    hi.continuousOn_mul (by unfold dirichletKernel; fun_prop)
  have hk (t : ℝ) : fejerKernel N t • f (x - t) =
      (1 / (N + 1 : ℝ)) • ∑ n ∈ Finset.range (N + 1),
        (dirichletKernel n t : ℂ) * f (x - t) := by
    simp only [fejerKernel, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      ← Finset.sum_mul]
    ring
  simp_rw [hk]
  rw [intervalIntegral.integral_smul,
    intervalIntegral.integral_finsetSum (fun n _ => hd n)]
  unfold fejerMean
  simp_rw [fourierPartialSum_convolution hp hf]
  rw [← Finset.smul_sum, smul_comm]

/-- Affine reflection preserves the literal source Riemann predicate on every cut. -/
theorem periodic_riemann_reflected_source {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (x : ℝ)
    {c d : ℝ} (hcd : c ≤ d) :
    RiemannIntegrableComplex (fun t ↦ f (x - t)) c d := by
  apply Rudin.Support.RiemannAffine.periodic_hasComplexRSIntegral_reflected
    (a := -Real.pi) (by positivity : 0 < 2 * Real.pi) hp ?_ x hcd
  obtain ⟨z, hz⟩ := hf
  refine ⟨z, ?_⟩
  convert hz using 1 <;> ring

/-- The convolution has an actual tagged Riemann value, not only a Bochner value. -/
theorem exercise15_convolution_riemann {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    ∃ z, Rudin.Support.StieltjesComplex.HasComplexRSIntegral
      (fun t ↦ fejerKernel N t • f (x - t)) id (-Real.pi) Real.pi z ∧
      fejerMean f N x = (1 / (2 * Real.pi) : ℝ) • z := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  obtain ⟨u, hu⟩ := periodic_riemann_reflected_source hp hf x hab
  obtain ⟨v, hv⟩ := continuous_riemannIntegrableComplex hab
    (Complex.continuous_ofReal.comp (exercise15_continuous N)).continuousOn
  obtain ⟨z, hz⟩ := Rudin.Support.StieltjesComplex.exists_product hab hv hu
  have hz' : Rudin.Support.StieltjesComplex.HasComplexRSIntegral
      (fun t ↦ fejerKernel N t • f (x - t)) id (-Real.pi) Real.pi z := by
    simpa only [Complex.real_smul, Function.comp_apply] using hz
  refine ⟨z, hz', ?_⟩
  rw [exercise15_convolution hp hf, (complex_riemann_bridge hab hz').2]

/-- The analogous finite Dirichlet convolution also has its source Riemann value. -/
theorem fourierPartialSum_convolution_riemann {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    ∃ z, Rudin.Support.StieltjesComplex.HasComplexRSIntegral
      (fun t ↦ (dirichletKernel N t : ℂ) * f (x - t)) id (-Real.pi) Real.pi z ∧
      fourierPartialSum f N x = (1 / (2 * Real.pi) : ℝ) • z := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  obtain ⟨u, hu⟩ := periodic_riemann_reflected_source hp hf x hab
  obtain ⟨v, hv⟩ := continuous_riemannIntegrableComplex hab
    (show ContinuousOn (fun t ↦ (dirichletKernel N t : ℂ)) (Icc (-Real.pi) Real.pi) by
      unfold dirichletKernel; fun_prop)
  obtain ⟨z, hz⟩ := Rudin.Support.StieltjesComplex.exists_product hab hv hu
  refine ⟨z, hz, ?_⟩
  rw [fourierPartialSum_convolution hp hf, (complex_riemann_bridge hab hz).2]

theorem fejerKernel_even (N : ℕ) (x : ℝ) : fejerKernel N (-x) = fejerKernel N x := by
  simp only [fejerKernel, dirichletKernel, mul_neg, Real.cos_neg]

lemma fejerKernel_half_mass (N : ℕ) : (∫ t in (0 : ℝ)..Real.pi, fejerKernel N t) = Real.pi := by
  have he := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := Real.pi) (fejerKernel N)
  simp only [neg_zero, fejerKernel_even] at he
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((exercise15_continuous N).intervalIntegrable (-Real.pi) 0)
    ((exercise15_continuous N).intervalIntegrable 0 Real.pi)
  have hm := exercise15_mass N
  rw [← ha, ← he] at hm
  field_simp at hm
  linarith

/-- The proved off-zero estimate gives uniform concentration of the actual kernels. -/
theorem fejerKernel_uniform_off_zero (u : Set ℝ) (hu : IsOpen u) (h0 : 0 ∈ u) :
    TendstoUniformlyOn (fun N t => fejerKernel N t / Real.pi) 0 atTop (Icc (-Real.pi) Real.pi \ u) := by
  obtain ⟨r, hr, hru⟩ := Metric.isOpen_iff.mp hu 0 h0
  let δ := min r (Real.pi / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  have hδπ : δ ≤ Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have hcd : 0 < 1 - Real.cos δ := by
    have h := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hδ.le, hδπ⟩ hδ
    simp only [Real.cos_zero] at h
    linarith
  have hlim : Tendsto (fun N : ℕ => (2 / ((1 - Real.cos δ) * Real.pi)) *
      (1 / (N + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (2 / ((1 - Real.cos δ) * Real.pi))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with N hN
  intro x hx
  have hdx : δ ≤ |x| := by
    by_contra h
    apply hx.2
    apply hru
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (lt_of_not_ge h).trans_le (min_le_left _ _)
  have hxπ : |x| ≤ Real.pi := abs_le.mpr hx.1
  have hb := div_le_div_of_nonneg_right (exercise15_off_zero_bound N hδ hdx hxπ) Real.pi_pos.le
  have he : 2 / ((N + 1 : ℝ) * (1 - Real.cos δ)) / Real.pi =
      (2 / ((1 - Real.cos δ) * Real.pi)) * (1 / (N + 1 : ℝ)) := by
    field_simp
    <;> ring
  rw [he] at hb
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (exercise15_nonnegative N x) Real.pi_pos.le)] using hb.trans_lt hN

/-- Half-interval approximate-identity limit for integrable complex functions. -/
theorem fejerKernel_half_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} {a : E}
    (hg : IntegrableOn g (Ioc 0 Real.pi)) (ha : Tendsto g (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun N => ∫ t in (0 : ℝ)..Real.pi, (fejerKernel N t / Real.pi) • g t)
      atTop (𝓝 a) := by
  have h := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (μ := volume) (l := atTop) (x₀ := (0 : ℝ)) (s := Ioc 0 Real.pi) (t := Ioc 0 Real.pi)
    (φ := fun N t => fejerKernel N t / Real.pi)
    measurableSet_Ioc measurableSet_Ioc (Subset.refl _) self_mem_nhdsWithin
    measure_Ioc_lt_top.ne
    (Filter.Eventually.of_forall (fun N x hx => div_nonneg (exercise15_nonnegative N x) Real.pi_pos.le))
    (fun u hu h0 => (fejerKernel_uniform_off_zero u hu h0).mono (by
      intro x hx
      exact ⟨⟨by linarith [hx.1.1, Real.pi_pos], hx.1.2⟩, hx.2⟩))
    (by
      have he (N : ℕ) : (∫ x in Ioc (0 : ℝ) Real.pi, fejerKernel N x / Real.pi) = 1 := by
        rw [← intervalIntegral.integral_of_le Real.pi_pos.le,
          intervalIntegral.integral_div, fejerKernel_half_mass, div_self Real.pi_ne_zero]
      simpa only [he] using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))))
    (Filter.Eventually.of_forall (fun N => ((exercise15_continuous N).div_const Real.pi).aestronglyMeasurable))
    hg (by rwa [nhdsWithin_Ioc_eq_nhdsGT Real.pi_pos])
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le] using h

lemma fejer_reflected_integrable {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (x a b : ℝ) :
    IntervalIntegrable (fun t => f (x - t)) volume a b := by
  convert (periodic_riemann_intervalIntegrable hp hf (x - a) (x - b)).comp_sub_left x
    using 1 <;> ring

lemma fejer_translated_integrable {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (x a b : ℝ) :
    IntervalIntegrable (fun t => f (x + t)) volume a b := by
  convert (periodic_riemann_intervalIntegrable hp hf (x + a) (x + b)).comp_add_left x
    using 1 <;> ring

/-- Evenness converts the convolution to the average of the two sides. -/
lemma fejerMean_half_convolution {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    fejerMean f N x = ∫ t in (0 : ℝ)..Real.pi,
      (fejerKernel N t / Real.pi) • ((f (x - t) + f (x + t)) / 2) := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t => fejerKernel N t • f (x - t)) volume a b := by
    simpa only [Complex.real_smul, Function.comp_def] using
      (fejer_reflected_integrable hp hf x a b).continuousOn_mul
        (Complex.continuous_ofReal.comp (exercise15_continuous N)).continuousOn
  have hj : IntervalIntegrable
      (fun t => fejerKernel N t • f (x + t)) volume 0 Real.pi := by
    simpa only [Complex.real_smul, Function.comp_def] using
      (fejer_translated_integrable hp hf x 0 Real.pi).continuousOn_mul
        (Complex.continuous_ofReal.comp (exercise15_continuous N)).continuousOn
  have he := intervalIntegral.integral_comp_neg
    (a := (0 : ℝ)) (b := Real.pi) (fun t => fejerKernel N t • f (x - t))
  simp only [fejerKernel_even, sub_neg_eq_add, neg_zero] at he
  have hk (t : ℝ) : (fejerKernel N t / Real.pi) • ((f (x - t) + f (x + t)) / 2) =
      (1 / (2 * Real.pi) : ℝ) • (fejerKernel N t • f (x - t) + fejerKernel N t • f (x + t)) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  simp_rw [hk]
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_add (hi 0 Real.pi) hj,
    exercise15_convolution hp hf,
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-Real.pi) 0) (hi 0 Real.pi), ← he,
    add_comm]


/-- Uniform Fejer convergence. The peak-function proof uses nonnegativity,
unit mass, and the proved off-zero bound, as in the source hint. -/
theorem exercise15_uniform_fejer {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    TendstoUniformlyOn (fun N x => fejerMean f N x) f atTop (Icc (-Real.pi) Real.pi) := by
  let S := Icc (-Real.pi) Real.pi
  let G : ℝ → C(S, ℂ) := fun t =>
    ⟨fun x => (f ((x : ℝ) - t) + f ((x : ℝ) + t)) / 2, by fun_prop⟩
  have hG : Continuous G := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × S => (f ((p.2 : ℝ) - p.1) + f ((p.2 : ℝ) + p.1)) / 2)
    fun_prop
  have hlim := fejerKernel_half_limit (hG.intervalIntegrable (μ := volume) 0 Real.pi).1
    (hG.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have hri : RiemannIntegrableComplex f (-Real.pi) Real.pi :=
    continuous_riemannIntegrableComplex (by linarith [Real.pi_pos]) hf.continuousOn
  have heval (N : ℕ) (x : S) :
      (∫ t in (0 : ℝ)..Real.pi, (fejerKernel N t / Real.pi) • G t) x = fejerMean f N x := by
    have hi : IntervalIntegrable (fun t => (fejerKernel N t / Real.pi) • G t) volume 0 Real.pi :=
      (((exercise15_continuous N).div_const Real.pi).smul hG).intervalIntegrable _ _
    have he := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hi
    change (∫ t in (0 : ℝ)..Real.pi, (fejerKernel N t / Real.pi) • G t x) =
      (∫ t in (0 : ℝ)..Real.pi, (fejerKernel N t / Real.pi) • G t) x at he
    rw [← he]
    exact (fejerMean_half_convolution hp hri N x).symm
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim
  convert hu using 1
  · ext N x
    exact (heval N x).symm
  · ext x
    dsimp [G]
    simp only [sub_zero, add_zero]
    ring

lemma symmetric_int_sum (h : ℤ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), h n) =
      h 0 + ∑ k ∈ Finset.range N, (h (k + 1) + h (-(k + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have he : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    rw [he, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    push_cast
    ring

theorem dirichletKernel_eq_int_sum (N : ℕ) (x : ℝ) :
    (dirichletKernel N x : ℂ) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierMonomial n x := by
  rw [symmetric_int_sum, dirichletKernel_complex]
  simp [fourierMonomial]

theorem fourierPartialSum_eq_int_sum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fourierCoefficient (-Real.pi) f n * fourierMonomial n x := by
  rw [symmetric_int_sum]
  simp only [fourierPartialSum, fourierMonomial, Int.cast_zero, mul_zero, zero_mul,
    Complex.exp_zero, mul_one]


/-- The source coefficient is the normalization of an actual tagged Riemann integral. -/
theorem fourierCoefficient_riemann {f : ℝ → ℂ}
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (n : ℤ) :
    ∃ z : ℂ, Rudin.Support.StieltjesComplex.HasComplexRSIntegral
      (fun x => fourierMonomial (-n) x * f x) id (-Real.pi) Real.pi z ∧
      fourierCoefficient (-Real.pi) f n = (1 / (2 * Real.pi) : ℝ) • z := by
  obtain ⟨w, hw⟩ := hf
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  obtain ⟨v, hv⟩ := continuous_riemannIntegrableComplex hab
    (f := fourierMonomial (-n)) (by unfold fourierMonomial; fun_prop)
  obtain ⟨z, hz⟩ := Rudin.Support.StieltjesComplex.exists_product hab hv hw
  refine ⟨z, hz, ?_⟩
  unfold fourierCoefficient
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, (complex_riemann_bridge hab hz).2]


end Rudin.Chapter08
