module

public import Math.Rudin.Chapter09.Exercise29
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Exercise 30: coordinate Taylor expansions

The source is book pages 243–244, primary PDF pages 252–253. The scalar
line restriction has an actual derivative jet before its total iterated
derivatives are used. One-variable Taylor theory gives both Lagrange and
integral remainders. A local bound on the continuous `m`th differential gives
the stated little-o remainder. Frequency fibers then convert the ordered
polynomial to one sum over nonnegative multi-indices of degree at most `m-1`.
-/

@[expose] public section
open Set Filter Finset
open scoped Topology BigOperators
namespace Rudin.Chapter09

/-- The ordered coordinate derivative agrees with the actual higher differential. -/
theorem mixedPartial_eq_iteratedFDeriv {n m k : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (hk : k ≤ m) (i : Fin k → Fin n) {a : CoordinateSpace n} (ha : a ∈ E) :
    mixedPartial (List.ofFn i) f a =
      iteratedFDeriv ℝ k f a (fun j => coordinateVector (i j)) := by
  induction k generalizing a with
  | zero => simp [mixedPartial, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (mixedPartial (List.ofFn (fun j => i j.succ)) f) a
      (coordinateVector (i 0)) = _
    have hd := (hf.contDiffAt (hE.mem_nhds ha)).differentiableAt_iteratedFDeriv
      (m := k) (by exact_mod_cast (show k < m by omega))
    rw [hd.iteratedFDeriv_succ_apply_left']
    apply congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (coordinateVector (i 0)))
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hE.mem_nhds ha] with b hb
    exact ih (by omega) (fun j => i j.succ) hb

noncomputable def orderedCoordinateSum {n : ℕ} (f : CoordinateSpace n → ℝ)
    (k : ℕ) (a x : CoordinateSpace n) : ℝ :=
  ∑ i : Fin k → Fin n, mixedPartial (List.ofFn i) f a * ∏ j, x (i j)

/-- Multilinearity expands a diagonal evaluation into all ordered coordinate tuples. -/
theorem orderedCoordinateSum_eq {n m k : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (hk : k ≤ m) {a : CoordinateSpace n} (ha : a ∈ E) (x : CoordinateSpace n) :
    orderedCoordinateSum f k a x = iteratedFDeriv ℝ k f a (fun _ => x) := by
  classical
  have hx : (∑ i : Fin n, x i • coordinateVector i) = x := by
    simpa [coordinateVector, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  conv_rhs => rw [← hx]
  rw [ContinuousMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousMultilinearMap.map_smul_univ,
    mixedPartial_eq_iteratedFDeriv hE hf hk i ha]
  exact mul_comm _ _

/-- The scalar derivative jet exists on the full inverse image of the open set. -/
theorem exercise30_sourceJet {n m k : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (hk : k < m) (a x : CoordinateSpace n) {t : ℝ} (ht : a + t • x ∈ E) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ k f (a + s • x) (fun _ => x))
      (iteratedFDeriv ℝ (k + 1) f (a + t • x) (fun _ => x)) t := by
  have hc := hf.contDiffAt (hE.mem_nhds ht)
  have hd := hc.differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast hk)
  have hds : DifferentiableAt ℝ
      (fun s : ℝ => iteratedFDeriv ℝ k f (a + s • x) (fun _ => x)) t := by
    simpa only [Function.comp_def] using
      (hd.continuousMultilinear_apply_const (fun _ => x)).comp t
        (show DifferentiableAt ℝ (fun s : ℝ => a + s • x) t by fun_prop)
  have hc' : ContDiffAt ℝ (k + 1) f (a + t • x) :=
    hc.of_le (by exact_mod_cast (show k + 1 ≤ m by omega))
  convert hds.hasDerivAt using 1
  exact hc'.deriv_fderiv_add_smul.symm

/-- The jet is the iterated scalar derivative, not only a formal diagonal expression. -/
theorem line_iteratedDeriv {n m k : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (hk : k ≤ m) (a x : CoordinateSpace n) {t : ℝ} (ht : a + t • x ∈ E) :
    iteratedDeriv k (fun s : ℝ => f (a + s • x)) t =
      iteratedFDeriv ℝ k f (a + t • x) (fun _ => x) := by
  induction k generalizing t with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s : ℝ => f (a + s • x)) =ᶠ[𝓝 t]
        (fun s : ℝ => iteratedFDeriv ℝ k f (a + s • x) (fun _ => x)) := by
      have hn : ∀ᶠ s in 𝓝 t, a + s • x ∈ E :=
        (show ContinuousAt (fun s : ℝ => a + s • x) t by fun_prop).preimage_mem_nhds
          (hE.mem_nhds ht)
      filter_upwards [hn] with s hs
      exact ih (by omega) hs
    rw [he.deriv_eq]
    exact (exercise30_sourceJet hE hf (by omega) a x ht).deriv

/-- Exercise 30(a), at every parameter whose point belongs to `E`. -/
theorem exercise30_a {n m k : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (hk : k ≤ m) (a x : CoordinateSpace n) {t : ℝ} (ht : a + t • x ∈ E) :
    iteratedDeriv k (fun s : ℝ => f (a + s • x)) t =
      ∑ i : Fin k → Fin n, mixedPartial (List.ofFn i) f (a + t • x) * ∏ j, x (i j) := by
  rw [line_iteratedDeriv hE hf hk a x ht]
  exact (orderedCoordinateSum_eq hE hf hk ht x).symm

noncomputable def orderedTaylorPolynomial {n : ℕ} (f : CoordinateSpace n → ℝ)
    (m : ℕ) (a x : CoordinateSpace n) : ℝ :=
  ∑ k ∈ range m, (k.factorial : ℝ)⁻¹ * orderedCoordinateSum f k a x

noncomputable def taylorRemainder {n : ℕ} (f : CoordinateSpace n → ℝ)
    (m : ℕ) (a x : CoordinateSpace n) : ℝ :=
  f (a + x) - orderedTaylorPolynomial f m a x

/-- Taylor's integral remainder, obtained by one-variable Taylor theory along the segment. -/
theorem exercise30_b_expansion {n m : ℕ} (hm : 1 ≤ m) {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    {a : CoordinateSpace n} (ha : a ∈ E) (x : CoordinateSpace n)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, a + t • x ∈ E) :
    f (a + x) = orderedTaylorPolynomial f m a x + taylorRemainder f m a x ∧
    taylorRemainder f m a x = ((m - 1).factorial : ℝ)⁻¹ *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ (m - 1) *
        iteratedFDeriv ℝ m f (a + t • x) (fun _ => x) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := p)
    (f := f) (x := a) (y := x) (fun t ht => by
      simpa using hf.contDiffAt (hE.mem_nhds (hx t ht)))
  have hp : orderedTaylorPolynomial f (p + 1) a x =
      ∑ k ∈ range (p + 1), (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k f a (fun _ => x) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [orderedCoordinateSum_eq hE hf (by simpa using (le_of_lt (mem_range.mp hk))) ha]
  simp only [smul_eq_mul] at hT
  constructor
  · simp [taylorRemainder]
  · simpa only [taylorRemainder, hp, Nat.succ_sub_one, Nat.succ_eq_add_one] using
      (sub_eq_iff_eq_add.mpr (hT.trans (add_comm _ _)))

@[simp] theorem orderedCoordinateSum_zero {n : ℕ} (f : CoordinateSpace n → ℝ)
    (a x : CoordinateSpace n) : orderedCoordinateSum f 0 a x = f a := by
  simp [orderedCoordinateSum, mixedPartial]

/-- The Lagrange remainder in the source's one-variable Taylor argument. -/
theorem exercise30_b_lagrange {n m : ℕ} (hm : 1 ≤ m) {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    {a : CoordinateSpace n} (ha : a ∈ E) (x : CoordinateSpace n)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, a + t • x ∈ E) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      taylorRemainder f m a x = orderedCoordinateSum f m (a + t • x) x / m.factorial := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let h : ℝ → ℝ := fun t => f (a + t • x)
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (p + 1) h t := by
    intro t ht
    simpa only [h, Function.comp_def] using
      (hf.contDiffAt (hE.mem_nhds (hx t ht))).comp t
        (show ContDiffAt ℝ (p + 1) (fun s : ℝ => a + s • x) t by fun_prop)
  have hdon : ContDiffOn ℝ (p + 1) h (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun t ht => (hd t ht).contDiffWithinAt
  obtain ⟨t, ht, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := p) (by norm_num : (0 : ℝ) ≠ 1) hdon
  have hp : taylorWithinEval h p (uIcc (0 : ℝ) 1) 0 1 =
      orderedTaylorPolynomial f (p + 1) a x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ p + 1 := (mem_range.mp hk).le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      ((hd 0 (by norm_num)).of_le (by exact_mod_cast hk')) (by norm_num)]
    simp only [sub_zero, one_pow, mul_one, smul_eq_mul]
    change _ = (k.factorial : ℝ)⁻¹ * orderedCoordinateSum f k a x
    congr 1
    simpa only [h, zero_smul, add_zero, orderedCoordinateSum] using
      exercise30_a hE hf hk' a x (t := 0) (by simpa using ha)
  rw [hp] at hTaylor
  rw [uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] at ht
  refine ⟨t, ht, ?_⟩
  simpa only [taylorRemainder, h, one_smul, sub_zero, one_pow, mul_one,
    exercise30_a hE hf le_rfl a x (hx t ⟨ht.1.le, ht.2.le⟩), orderedCoordinateSum] using hTaylor

/-- The remainder integrand is continuous on the full segment, hence integrable. -/
theorem taylorRemainder_intervalIntegrable {n m : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (a x : CoordinateSpace n) (hx : ∀ t ∈ Icc (0 : ℝ) 1, a + t • x ∈ E) :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (m - 1) *
      iteratedFDeriv ℝ m f (a + t • x) (fun _ => x)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro t ht
  have hc := ((hf.contDiffAt (hE.mem_nhds (hx t ht))).iteratedFDeriv_right
    (i := m) (m := 0) (by simp)).continuousAt
  have hv : ContinuousAt (fun s : ℝ =>
      iteratedFDeriv ℝ m f (a + s • x) (fun _ => x)) t :=
    (hc.comp (x := t) (show ContinuousAt (fun s : ℝ => a + s • x) t by fun_prop)).eval_const _
  exact ((show ContinuousAt (fun s : ℝ => (1 - s) ^ (m - 1)) t by fun_prop).mul hv).continuousWithinAt

/-- A uniform local bound uses only continuity of the source's `m`th derivative. -/
theorem taylorRemainder_isBigO {n m : ℕ} (hm : 1 ≤ m) {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    {a : CoordinateSpace n} (ha : a ∈ E) :
    Asymptotics.IsBigO (𝓝 0) (taylorRemainder f m a) (fun x => ‖x‖ ^ m) := by
  let C : ℝ := ‖iteratedFDeriv ℝ m f a‖ + 1
  have hc : ContinuousAt (iteratedFDeriv ℝ m f) a :=
    ((hf.contDiffAt (hE.mem_nhds ha)).iteratedFDeriv_right
      (i := m) (m := 0) (by simp)).continuousAt
  have hn : ∀ᶠ y in 𝓝 a, y ∈ E ∧ ‖iteratedFDeriv ℝ m f y‖ < C := by
    exact (show ∀ᶠ y in 𝓝 a, y ∈ E from hE.mem_nhds ha).and
      (hc.norm.preimage_mem_nhds (Iio_mem_nhds (by dsimp [C]; linarith)))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hn
  apply Asymptotics.IsBigO.of_bound (‖((m - 1).factorial : ℝ)⁻¹‖ * C)
  filter_upwards [Metric.ball_mem_nhds (0 : CoordinateSpace n) hδ] with x hx
  have hxδ : ‖x‖ < δ := by simpa [Metric.mem_ball] using hx
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, dist (a + t • x) a < δ := by
    intro t ht
    calc
      dist (a + t • x) a = ‖t • x‖ := by simp [dist_eq_norm]
      _ = t * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1]
      _ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
      _ < δ := hxδ
  have he : ∀ t ∈ Icc (0 : ℝ) 1, a + t • x ∈ E :=
    fun t ht => (hb (hseg t ht)).1
  have hI : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ (m - 1) *
      iteratedFDeriv ℝ m f (a + t • x) (fun _ => x)‖ ≤ C * ‖x‖ ^ m := by
    have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖(1 - t) ^ (m - 1) * iteratedFDeriv ℝ m f (a + t • x) (fun _ => x)‖ ≤
          C * ‖x‖ ^ m := by
      intro t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hpow : ‖(1 - t) ^ (m - 1)‖ ≤ 1 := by
        rw [norm_pow, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
        exact pow_le_one₀ (sub_nonneg.mpr ht.2) (by linarith [ht.1])
      have hmulti := (iteratedFDeriv ℝ m f (a + t • x)).le_opNorm (fun _ => x)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmulti
      calc
        _ = ‖(1 - t) ^ (m - 1)‖ *
            ‖iteratedFDeriv ℝ m f (a + t • x) (fun _ => x)‖ := norm_mul _ _
        _ ≤ ‖iteratedFDeriv ℝ m f (a + t • x) (fun _ => x)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hpow
        _ ≤ ‖iteratedFDeriv ℝ m f (a + t • x)‖ * ‖x‖ ^ m := hmulti
        _ ≤ C * ‖x‖ ^ m :=
          mul_le_mul_of_nonneg_right (hb (hseg t ht')).2.le (by positivity)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [(exercise30_b_expansion hm hE hf ha x he).2, norm_mul]
  calc
    _ ≤ ‖((m - 1).factorial : ℝ)⁻¹‖ * (C * ‖x‖ ^ m) :=
      mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = (‖((m - 1).factorial : ℝ)⁻¹‖ * C) * ‖‖x‖ ^ m‖ := by
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) m)]; ring

/-- Exercise 30(b): the actual remainder is little-o of the Euclidean norm to degree `m-1`. -/
theorem exercise30_b_remainder_isLittleO {n m : ℕ} (hm : 1 ≤ m)
    {E : Set (CoordinateSpace n)} (hE : IsOpen E) {f : CoordinateSpace n → ℝ}
    (hf : ContDiffOn ℝ m f E) {a : CoordinateSpace n} (ha : a ∈ E) :
    Asymptotics.IsLittleO (𝓝 0) (taylorRemainder f m a) (fun x => ‖x‖ ^ (m - 1)) :=
  (taylorRemainder_isBigO hm hE hf ha).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_norm_pow (by omega))

/-- The source's punctured limit, also valid for `m=1` and dimension zero. -/
theorem exercise30_b_remainder {n m : ℕ} (hm : 1 ≤ m)
    {E : Set (CoordinateSpace n)} (hE : IsOpen E) {f : CoordinateSpace n → ℝ}
    (hf : ContDiffOn ℝ m f E) {a : CoordinateSpace n} (ha : a ∈ E) :
    Tendsto (fun x => taylorRemainder f m a x / ‖x‖ ^ (m - 1))
      (𝓝[≠] (0 : CoordinateSpace n)) (𝓝 0) :=
  (exercise30_b_remainder_isLittleO hm hE hf ha).tendsto_div_nhds_zero.mono_left
    nhdsWithin_le_nhds

/-- All nonnegative coordinate multi-indices of total degree less than `m`. -/
noncomputable def taylorMultiIndices (n m : ℕ) : Finset (Fin n → ℕ) := by
  classical
  exact (range m).biUnion (piAntidiag univ)

theorem mem_taylorMultiIndices {n m : ℕ} (s : Fin n → ℕ) :
    s ∈ taylorMultiIndices n m ↔ (∑ i, s i) < m := by
  classical
  simp [taylorMultiIndices, Finset.mem_piAntidiag]

/-- The source's inclusive degree bound, including its `m=1` case. -/
theorem mem_taylorMultiIndices_iff {n m : ℕ} (hm : 1 ≤ m) (s : Fin n → ℕ) :
    s ∈ taylorMultiIndices n m ↔ (∑ i, s i) ≤ m - 1 := by
  rw [mem_taylorMultiIndices]; omega

theorem sum_taylorMultiIndices {n m : ℕ} (W : (Fin n → ℕ) → ℝ) :
    (∑ s ∈ taylorMultiIndices n m, W s) =
      ∑ k ∈ range m, ∑ s ∈ piAntidiag univ k, W s := by
  classical
  apply Finset.sum_biUnion
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro s hi hj
  exact hij ((Finset.mem_piAntidiag.mp hi).1.symm.trans
    (Finset.mem_piAntidiag.mp hj).1)

/-! Counting is kept with the expansion that uses it. The fiber cardinality
is proved by comparing coefficients in two proved polynomial expansions. -/
namespace Exercise30Combinatorics

/-- The number of occurrences of `i` in the ordered tuple `t`. -/
def counts {n k : ℕ} (t : Fin k → Fin n) (i : Fin n) : ℕ :=
  (univ.filter fun j => t j = i).card

private theorem exponent_eq {n k : ℕ} (t : Fin k → Fin n) :
    (∑ j, Finsupp.single (t j) 1) =
      Finsupp.equivFunOnFinite.symm (counts t) := by
  ext i
  simp [counts, Finsupp.single_apply, eq_comm]

private theorem indicator_eq {n : ℕ} (s : Fin n → ℕ) :
    Finsupp.indicator univ (fun i _ => s i) = Finsupp.equivFunOnFinite.symm s := by
  ext i
  simp

/-- Exact number of ordered tuples with prescribed coordinate multiplicities. -/
theorem card_counts_fiber {n k : ℕ} (s : Fin n → ℕ) (hs : ∑ i, s i = k) :
    (univ.filter fun t : Fin k → Fin n => counts t = s).card =
      k.factorial / ∏ i, (s i).factorial := by
  classical
  let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm s
  have h := congrArg (fun p : MvPolynomial (Fin n) ℕ => p.coeff d)
    (Finset.sum_pow_eq_sum_piAntidiag univ (fun i => MvPolynomial.X i) k)
  have hleft : ((∑ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) ℕ) ^ k).coeff d =
      (univ.filter fun t : Fin k → Fin n => counts t = s).card := by
    rw [Fintype.sum_pow]
    simp_rw [MvPolynomial.X, ← MvPolynomial.monomial_sum_one, exponent_eq]
    simp [MvPolynomial.coeff_monomial, d,
      Finsupp.equivFunOnFinite.symm.injective.eq_iff, eq_comm]
  rw [hleft] at h
  rw [h]
  simp_rw [MvPolynomial.coeff_sum, ← map_natCast MvPolynomial.C,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_prod_X_pow, indicator_eq]
  simp only [d, Finsupp.equivFunOnFinite.symm.injective.eq_iff]
  simp [Finset.mem_piAntidiag, hs, Nat.multinomial]

/-- Every position contributes once to the total multiplicity. -/
theorem sum_counts {n k : ℕ} (t : Fin k → Fin n) : ∑ i, counts t i = k := by
  simp only [counts, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- Group any function of the multiplicities by its exact number of ordered realizations. -/
theorem sum_counts_weight {n k : ℕ} {A : Type*} [AddCommMonoid A]
    (W : (Fin n → ℕ) → A) :
    (∑ t : Fin k → Fin n, W (counts t)) =
      ∑ s ∈ piAntidiag univ k, (k.factorial / ∏ i, (s i).factorial) • W s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := univ) (t := piAntidiag univ k) (g := counts)
    (fun t _ => by simp [sum_counts])]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : ∑ i, s i = k := (Finset.mem_piAntidiag.mp hs).1
  rw [← card_counts_fiber s hs', ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

/-- Coordinate indices in ascending blocks, with the specified repetitions. -/
def canonicalAscending {n : ℕ} (s : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun i => List.replicate (s i) i

theorem length_canonicalAscending {n : ℕ} (s : Fin n → ℕ) :
    (canonicalAscending s).length = ∑ i, s i := by
  simp [canonicalAscending, List.length_flatMap, ← Fin.sum_univ_def]

theorem count_canonicalAscending {n : ℕ} (s : Fin n → ℕ) (i : Fin n) :
    (canonicalAscending s).count i = s i := by
  simp [canonicalAscending, List.count_flatMap, List.count_replicate,
    Function.comp_def, ← Fin.sum_univ_def]

theorem count_ofFn {n k : ℕ} (t : Fin k → Fin n) (i : Fin n) :
    (List.ofFn t).count i = counts t i := by
  rw [List.ofFn_eq_map, List.count_eq_countP, List.countP_map]
  simp only [Function.comp_def]
  rw [counts, ← List.toFinset_finRange k, (List.nodup_finRange k).card_eq_countP]
  congr 1

theorem ofFn_perm_canonicalAscending {n k : ℕ} (t : Fin k → Fin n) :
    (List.ofFn t).Perm (canonicalAscending (counts t)) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [count_ofFn, count_canonicalAscending]

/-- Products over tuple positions group by their coordinate multiplicities. -/
theorem prod_eq_prod_pow_counts {n k : ℕ} {M : Type*} [CommMonoid M]
    (x : Fin n → M) (t : Fin k → Fin n) :
    (∏ j, x (t j)) = ∏ i, x i ^ counts t i := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := univ) (t := univ)
    (g := t) (fun _ _ => Finset.mem_univ _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [counts, ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

/-- Exact source-facing grouping, with the ascending coordinate list. -/
theorem sum_list_perm_invariant {n k : ℕ}
    (F : List (Fin n) → ℝ)
    (hF : ∀ (l l' : List (Fin n)), l.length = k → l.Perm l' → F l = F l')
    (x : Fin n → ℝ) :
    (∑ t : Fin k → Fin n, F (List.ofFn t) * ∏ j, x (t j)) =
      ∑ s ∈ piAntidiag univ k,
        ((k.factorial : ℝ) / (∏ i, (s i).factorial : ℕ)) *
          F (canonicalAscending s) * ∏ i, x i ^ s i := by
  classical
  calc
    _ = ∑ t : Fin k → Fin n,
        F (canonicalAscending (counts t)) * ∏ i, x i ^ counts t i := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hF _ _ (List.length_ofFn) (ofFn_perm_canonicalAscending t),
        prod_eq_prod_pow_counts]
    _ = ∑ s ∈ piAntidiag univ k,
        (k.factorial / ∏ i, (s i).factorial) •
          (F (canonicalAscending s) * ∏ i, x i ^ s i) :=
      sum_counts_weight (k := k) (fun s => F (canonicalAscending s) * ∏ i, x i ^ s i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : ∑ i, s i = k := (Finset.mem_piAntidiag.mp hs).1
      have hd : (∏ i, (s i).factorial) ∣ k.factorial := by
        simpa [hs'] using Nat.prod_factorial_dvd_factorial_sum univ s
      rw [nsmul_eq_mul, Nat.cast_div_charZero hd, mul_assoc]

end Exercise30Combinatorics

/-- `D₁^s₁ ... Dₙ^sₙ f`, with the coordinate blocks in increasing order. -/
noncomputable def multiIndexPartial {n : ℕ} (s : Fin n → ℕ)
    (f : CoordinateSpace n → ℝ) : CoordinateSpace n → ℝ :=
  mixedPartial (Exercise30Combinatorics.canonicalAscending s) f

noncomputable def multiIndexTaylorPolynomial {n : ℕ} (f : CoordinateSpace n → ℝ)
    (m : ℕ) (a x : CoordinateSpace n) : ℝ :=
  ∑ s ∈ taylorMultiIndices n m,
    multiIndexPartial s f a / (∏ i, (s i).factorial : ℕ) * ∏ i, x i ^ s i

/-- Exercise 30(c). Counting each frequency fiber rewrites the same polynomial. -/
theorem exercise30_c {n m : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    {a : CoordinateSpace n} (ha : a ∈ E) (x : CoordinateSpace n) :
    orderedTaylorPolynomial f m a x = multiIndexTaylorPolynomial f m a x := by
  classical
  rw [multiIndexTaylorPolynomial, sum_taylorMultiIndices]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m := (mem_range.mp hk).le
  have hgroup := Exercise30Combinatorics.sum_list_perm_invariant
    (k := k) (fun l => mixedPartial l f a)
    (fun l q hl hp => exercise29_permutation_invariance hE hf hp (hl ▸ hk') ha)
    (fun i => x i)
  change (k.factorial : ℝ)⁻¹ * orderedCoordinateSum f k a x = _
  rw [orderedCoordinateSum, hgroup, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
  change (k.factorial : ℝ)⁻¹ *
    (((k.factorial : ℝ) / (∏ i, (s i).factorial : ℕ)) * multiIndexPartial s f a *
      ∏ i, x i ^ s i) = _
  field_simp

/-- Both source polynomials have the identical remainder, on every permitted segment. -/
theorem exercise30_multiIndex_expansion {n m : ℕ} (hm : 1 ≤ m)
    {E : Set (CoordinateSpace n)} (hE : IsOpen E) {f : CoordinateSpace n → ℝ}
    (hf : ContDiffOn ℝ m f E) {a : CoordinateSpace n} (ha : a ∈ E)
    (x : CoordinateSpace n) (hx : ∀ t ∈ Icc (0 : ℝ) 1, a + t • x ∈ E) :
    f (a + x) =
      (∑ s ∈ taylorMultiIndices n m,
        multiIndexPartial s f a / (∏ i, (s i).factorial : ℕ) * ∏ i, x i ^ s i) +
      taylorRemainder f m a x := by
  rw [← multiIndexTaylorPolynomial, ← exercise30_c hE hf ha x]
  exact (exercise30_b_expansion hm hE hf ha x hx).1

end Rudin.Chapter09
