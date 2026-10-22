module

public import Math.Rudin.Support.StieltjesRefinement

/-!
A continuous-integrand bridge for the actual closed-cell Darboux sums.
The integrator is a `StieltjesFunction`: its right continuity is essential.
The measure integral uses `(a,b]`, excluding any atom at the initial endpoint.
Source: Rudin, book pages 120–125 (PDF pages 129–134).
-/

@[expose] public section

namespace Rudin.Support.StieltjesMeasureBridge

open Set MeasureTheory StieltjesPrototype StieltjesRefinement

variable {a b : ℝ}

/-- The constant integral uses the actual endpoint values of the integrator. -/
theorem integral_const (α : StieltjesFunction ℝ) (hab : a ≤ b) (c : ℝ) :
    (∫ _ in a..b, c ∂α.measure) = c * (α b - α a) := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.setIntegral_const,
    Measure.real, α.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (α.mono hab))]
  simp [smul_eq_mul, mul_comm]

/-- Continuous functions are integrable for the Stieltjes measure on each cell. -/
theorem cell_integrable (α : StieltjesFunction ℝ) (p : Partition a b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) {i : ℕ} (hi : i < p.n) :
    IntervalIntegrable f α.measure (p.x i) (p.x (i + 1)) :=
  (hf.mono (cell_subset p hi)).intervalIntegrable_of_Icc (left_isTag p i hi).2

/-- Finite additivity is valid even with repeated nodes. -/
theorem sum_cell_integrals (α : StieltjesFunction ℝ) (p : Partition a b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    (∑ i ∈ Finset.range p.n, ∫ x in p.x i..p.x (i + 1), f x ∂α.measure) =
      ∫ x in a..b, f x ∂α.measure := by
  simpa only [p.first, p.last] using
    intervalIntegral.sum_integral_adjacent_intervals (a := p.x) (n := p.n)
      (fun i hi ↦ cell_integrable α p hf hi)

/-- Every actual lower sum is below the measure integral. -/
theorem lowerSum_le_integral (α : StieltjesFunction ℝ) (p : Partition a b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    lowerSum p f α ≤ ∫ x in a..b, f x ∂α.measure := by
  rw [← sum_cell_integrals α p hf]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hle := (left_isTag p i hi').2
  rw [← integral_const α hle]
  apply intervalIntegral.integral_mono_on hle intervalIntegrable_const (cell_integrable α p hf hi')
  intro x hx
  exact csInf_le (isCompact_Icc.bddBelow_image (hf.mono (cell_subset p hi')))
    (mem_image_of_mem f hx)

/-- Every actual upper sum is above the measure integral. -/
theorem integral_le_upperSum (α : StieltjesFunction ℝ) (p : Partition a b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x ∂α.measure) ≤ upperSum p f α := by
  rw [← sum_cell_integrals α p hf]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hle := (left_isTag p i hi').2
  rw [← integral_const α hle]
  apply intervalIntegral.integral_mono_on hle (cell_integrable α p hf hi') intervalIntegrable_const
  intro x hx
  exact le_csSup (isCompact_Icc.bddAbove_image (hf.mono (cell_subset p hi')))
    (mem_image_of_mem f hx)

/-- A uniform grid; unused nodes need not be in the interval. -/
noncomputable def uniformGrid (hab : a ≤ b) (n : ℕ) (hn : 0 < n) : Partition a b where
  n := n
  pos := hn
  x := fun i ↦ a + (i : ℝ) * ((b - a) / n)
  first := by simp
  last := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [mul_div_cancel₀, hn']
  increasing := by
    intro i _ j _ hij
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij)
      (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg n)))

/-- The closed cells of a uniform grid have the specified length. -/
theorem uniformGrid_cell_length (hab : a ≤ b) (n : ℕ) (hn : 0 < n) (i : ℕ) :
    (uniformGrid hab n hn).x (i + 1) - (uniformGrid hab n hn).x i = (b - a) / n := by
  simp only [uniformGrid, Nat.cast_add, Nat.cast_one]
  ring

/-- A bound on the oscillation in each closed cell bounds the Darboux gap.
No strict increase of the integrator or the partition is required. -/
theorem darboux_gap_le (p : Partition a b) {f α : ℝ → ℝ} {δ : ℝ}
    (hα : MonotoneOn α (Icc a b))
    (hosc : ∀ i < p.n, ∀ x ∈ Icc (p.x i) (p.x (i + 1)),
      ∀ y ∈ Icc (p.x i) (p.x (i + 1)), f x - f y ≤ δ) :
    upperSum p f α - lowerSum p f α ≤ δ * (α b - α a) := by
  have htel := Finset.sum_range_sub (fun i ↦ α (p.x i)) p.n
  rw [p.first, p.last] at htel
  rw [upperSum, lowerSum, ← Finset.sum_sub_distrib, ← htel, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hne : (f '' Icc (p.x i) (p.x (i + 1))).Nonempty :=
    ⟨_, mem_image_of_mem f (left_isTag p i hi')⟩
  have hgap : sSup (f '' Icc (p.x i) (p.x (i + 1))) -
      sInf (f '' Icc (p.x i) (p.x (i + 1))) ≤ δ := by
    rw [sub_le_iff_le_add]
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    have hlow : f x - δ ≤ sInf (f '' Icc (p.x i) (p.x (i + 1))) := by
      apply le_csInf hne
      rintro _ ⟨y, hy, rfl⟩
      linarith [hosc i hi' x hx y hy]
    linarith
  simpa only [← sub_mul] using
    mul_le_mul_of_nonneg_right hgap (increment_nonneg p hα hi')

/-- Uniform continuity gives weak partitions with arbitrarily small Darboux gaps,
even for a raw monotone integrator. This is not a raw-integrator measure bridge. -/
theorem exists_small_darboux_gap (hab : a ≤ b) {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ContinuousOn f (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Partition a b, upperSum p f α - lowerSum p f α < ε := by
  have hmass : 0 ≤ α b - α a :=
    sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let η := ε / (α b - α a + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hnpos : 0 < n := by
    have : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.mpr hab) hδ.le
    exact_mod_cast (lt_of_le_of_lt this hn)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmesh : (b - a) / n < δ := by
    apply (div_lt_iff₀ hnreal).mpr
    have := (div_lt_iff₀ hδ).mp hn
    nlinarith
  let p := uniformGrid hab n hnpos
  have hgap := darboux_gap_le p hα (δ := η) (by
    intro i hi x hx y hy
    have hlen := uniformGrid_cell_length hab n hnpos i
    have hdist : dist x y < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> dsimp only [p] at hx hy <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h := hmod x (cell_subset p hi hx) y (cell_subset p hi hy) hdist
    rw [Real.dist_eq] at h
    exact (le_abs_self _).trans h.le)
  refine ⟨p, hgap.trans_lt ?_⟩
  have hscale : η * (α b - α a + 1) = ε :=
    div_mul_cancel₀ _ (by linarith)
  nlinarith

/-- Continuous integrands have an actual Darboux integral for every integrator
monotone on the interval. This existence result does not identify a measure integral. -/
theorem exists_hasDarbouxRSIntegral (hab : a ≤ b) {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ContinuousOn f (Icc a b)) :
    ∃ value : ℝ, HasDarbouxRSIntegral f α a b value := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.abs
  have hbound : ∀ x ∈ Icc a b, |f x| ≤ M :=
    fun x hx ↦ hM (mem_image_of_mem _ hx)
  let L := sSup (Set.range fun p : Partition a b ↦ lowerSum p f α)
  let U := sInf (Set.range fun p : Partition a b ↦ upperSum p f α)
  have hLU : L ≤ U := lowerIntegral_le_upperIntegral hab hα hbound
  have hUL : U ≤ L := by
    by_contra h
    obtain ⟨p, hp⟩ := exists_small_darboux_gap hab hα hf
      (sub_pos.mpr (lt_of_not_ge h))
    have hl : lowerSum p f α ≤ L :=
      le_csSup (lowerSum_range_bounded hα hbound).2 ⟨p, rfl⟩
    have hu : U ≤ upperSum p f α :=
      csInf_le (upperSum_range_bounded hα hbound).1 ⟨p, rfl⟩
    linarith
  exact ⟨L, hα, ⟨M, hbound⟩, rfl, le_antisymm hUL hLU⟩

/-- The actual Darboux integral of a continuous function equals its measure integral.
Right continuity comes from `StieltjesFunction`, not from a normalization of a raw
monotone function. The conclusion includes `a = b` and zero total mass. -/
theorem continuous_bridge (α : StieltjesFunction ℝ) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    HasDarbouxRSIntegral f α a b (∫ x in a..b, f x ∂α.measure) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.abs
  have hbound : ∀ x ∈ Icc a b, |f x| ≤ M :=
    fun x hx ↦ hM (mem_image_of_mem _ hx)
  have hα := α.mono.monotoneOn (Icc a b)
  let L := sSup (Set.range fun p : Partition a b ↦ lowerSum p f α)
  let U := sInf (Set.range fun p : Partition a b ↦ upperSum p f α)
  let I := ∫ x in a..b, f x ∂α.measure
  have hlne : (Set.range fun p : Partition a b ↦ lowerSum p f α).Nonempty :=
    ⟨_, ⟨single hab, rfl⟩⟩
  have hune : (Set.range fun p : Partition a b ↦ upperSum p f α).Nonempty :=
    ⟨_, ⟨single hab, rfl⟩⟩
  have hlI : L ≤ I := by
    apply csSup_le hlne
    rintro _ ⟨p, rfl⟩
    exact lowerSum_le_integral α p hf
  have hIu : I ≤ U := by
    apply le_csInf hune
    rintro _ ⟨p, rfl⟩
    exact integral_le_upperSum α p hf
  have hpL : ∀ p : Partition a b, lowerSum p f α ≤ L :=
    fun p ↦ le_csSup (lowerSum_range_bounded hα hbound).2 ⟨p, rfl⟩
  have hUp : ∀ p : Partition a b, U ≤ upperSum p f α :=
    fun p ↦ csInf_le (upperSum_range_bounded hα hbound).1 ⟨p, rfl⟩
  have hIl : I ≤ L := by
    by_contra h
    obtain ⟨p, hp⟩ := exists_small_darboux_gap hab hα hf (sub_pos.mpr (lt_of_not_ge h))
    have := hpL p
    have := integral_le_upperSum α p hf
    dsimp only [I] at *
    linarith
  have huI : U ≤ I := by
    by_contra h
    obtain ⟨p, hp⟩ := exists_small_darboux_gap hab hα hf (sub_pos.mpr (lt_of_not_ge h))
    have := hUp p
    have := lowerSum_le_integral α p hf
    dsimp only [I] at *
    linarith
  exact ⟨hα, ⟨M, hbound⟩, le_antisymm hlI hIl, le_antisymm huI hIu⟩

/-- The bridge also gives the refinement-based tagged-sum criterion. -/
theorem continuous_tagged_bridge (α : StieltjesFunction ℝ) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    HasRSIntegral f α a b (∫ x in a..b, f x ∂α.measure) :=
  hasRSIntegral_of_hasDarbouxRSIntegral hab (continuous_bridge α hab hf)

/-- Singleton regression: no continuity of the integrand is needed. -/
theorem bridge_self (α : StieltjesFunction ℝ) (f : ℝ → ℝ) (a : ℝ) :
    HasDarbouxRSIntegral f α a a (∫ x in a..a, f x ∂α.measure) := by
  simpa only [intervalIntegral.integral_same] using hasDarbouxRSIntegral_self f α a

/-- Zero total mass gives a zero integral, without a division by that mass. -/
theorem integral_eq_zero_of_endpoint_eq (α : StieltjesFunction ℝ) (hab : a ≤ b)
    (hmass : α b = α a) (f : ℝ → ℝ) :
    (∫ x in a..b, f x ∂α.measure) = 0 := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_measure_zero
  rw [α.measure_Ioc, hmass, sub_self, ENNReal.ofReal_zero]

/-- Zero-mass regression for the actual Darboux definition. -/
theorem continuous_bridge_zero_mass (α : StieltjesFunction ℝ) (hab : a ≤ b)
    (hmass : α b = α a) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    HasDarbouxRSIntegral f α a b 0 := by
  simpa only [integral_eq_zero_of_endpoint_eq α hab hmass f] using continuous_bridge α hab hf

/-- Repeated-node regression: an individual zero-length cell contributes zero. -/
theorem cell_integral_of_repeated (α : StieltjesFunction ℝ) (p : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hi : p.x (i + 1) = p.x i) :
    (∫ x in p.x i..p.x (i + 1), f x ∂α.measure) = 0 := by
  rw [hi, intervalIntegral.integral_same]

end Rudin.Support.StieltjesMeasureBridge
