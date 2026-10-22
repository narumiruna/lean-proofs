module

public import Math.Rudin.Support.StieltjesEquivalence

/-!
Algebra and order for Rudin's real Riemann–Stieltjes integrals.
Source: Theorems 6.12–6.13, book pages 128–129 (PDF 137–138); applications include
Chapter 6 Exercises 3, 7–12 and 15–17 (book pages 138–141).

The proofs use the original tagged sums and actual common refinements.
The Darboux laws follow from the proved predicate equivalence. No measure
substitution, right normalization, or continuity of the integrator is used.
All interval hypotheses allow `a = b`, repeated nodes, and zero increments.
This file does not supply complex integrands or integration by parts.
-/

@[expose] public section

namespace Rudin.Support.StieltjesIntegralLaws

open Set StieltjesPrototype StieltjesRefinement StieltjesEquivalence

variable {a b v w : ℝ} {f g α β : ℝ → ℝ}

theorem taggedSum_add (p : Partition a b) (f g α : ℝ → ℝ) (tag : ℕ → ℝ) :
    taggedSum p (fun x ↦ f x + g x) α tag =
      taggedSum p f α tag + taggedSum p g α tag := by
  simp [taggedSum, add_mul, Finset.sum_add_distrib]

theorem taggedSum_mul (p : Partition a b) (c : ℝ) (f α : ℝ → ℝ) (tag : ℕ → ℝ) :
    taggedSum p (fun x ↦ c * f x) α tag = c * taggedSum p f α tag := by
  simp [taggedSum, mul_assoc, Finset.mul_sum]

theorem taggedSum_integrator_add (p : Partition a b) (f α β : ℝ → ℝ) (tag : ℕ → ℝ) :
    taggedSum p f (fun x ↦ α x + β x) tag =
      taggedSum p f α tag + taggedSum p f β tag := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem taggedSum_integrator_mul (p : Partition a b) (c : ℝ) (f α : ℝ → ℝ)
    (tag : ℕ → ℝ) :
    taggedSum p f (fun x ↦ c * α x) tag = c * taggedSum p f α tag := by
  unfold taggedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One partition controls two actual tagged sums, also for different integrators. -/
theorem common_control (hf : HasRSIntegral f α a b v) (hg : HasRSIntegral g β a b w)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ p : Partition a b, ∀ q : Partition a b, Refines q p →
      ∀ tag : ℕ → ℝ, IsTag q tag →
        |taggedSum q f α tag - v| < ε ∧ |taggedSum q g β tag - w| < δ := by
  obtain ⟨p, hp⟩ := hf.2.2 ε hε
  obtain ⟨r, hr⟩ := hg.2.2 δ hδ
  refine ⟨commonRefinement p r, fun q hq tag ht ↦ ⟨?_, ?_⟩⟩
  · exact hp q (refines_trans hq (commonRefinement_refines_left p r)) tag ht
  · exact hr q (refines_trans hq (commonRefinement_refines_right p r)) tag ht

/-- Addition is proved by common refinement, not by a measure integral law. -/
theorem hasRSIntegral_add (hf : HasRSIntegral f α a b v) (hg : HasRSIntegral g α a b w) :
    HasRSIntegral (fun x ↦ f x + g x) α a b (v + w) := by
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨N, hN⟩ := hg.2.1
  refine ⟨hf.1, ⟨M + N, fun x hx ↦ (abs_add_le _ _).trans (add_le_add (hM x hx) (hN x hx))⟩, ?_⟩
  intro ε hε
  obtain ⟨p, hp⟩ := common_control hf hg (ε := ε / 2) (δ := ε / 2)
    (by linarith) (by linarith)
  refine ⟨p, fun q hq tag ht ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hp q hq tag ht
  rw [taggedSum_add]
  have h := abs_add_le (taggedSum q f α tag - v) (taggedSum q g α tag - w)
  have heq : taggedSum q f α tag + taggedSum q g α tag - (v + w) =
      (taggedSum q f α tag - v) + (taggedSum q g α tag - w) := by ring
  rw [heq]
  linarith

private theorem scaled_error {c t ε : ℝ} (hε : 0 < ε)
    (ht : |t| < ε / (|c| + 1)) : |c * t| < ε := by
  have hd : 0 < ε / (|c| + 1) := div_pos hε (by positivity)
  have hs : ε / (|c| + 1) * (|c| + 1) = ε :=
    div_mul_cancel₀ _ (by positivity)
  have hm := mul_le_mul_of_nonneg_left ht.le (abs_nonneg c)
  rw [abs_mul]
  nlinarith

/-- Integrand scaling permits every real scalar, including negative scalars. -/
theorem hasRSIntegral_mul (hf : HasRSIntegral f α a b v) (c : ℝ) :
    HasRSIntegral (fun x ↦ c * f x) α a b (c * v) := by
  obtain ⟨M, hM⟩ := hf.2.1
  refine ⟨hf.1, ⟨|c| * M, ?_⟩, ?_⟩
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg c)
  · intro ε hε
    obtain ⟨p, hp⟩ := hf.2.2 (ε / (|c| + 1)) (div_pos hε (by positivity))
    refine ⟨p, fun q hq tag ht ↦ ?_⟩
    rw [taggedSum_mul, ← mul_sub]
    exact scaled_error hε (hp q hq tag ht)

theorem hasRSIntegral_neg (hf : HasRSIntegral f α a b v) :
    HasRSIntegral (fun x ↦ -f x) α a b (-v) := by
  simpa only [neg_one_mul] using hasRSIntegral_mul hf (-1)

theorem hasRSIntegral_sub (hf : HasRSIntegral f α a b v) (hg : HasRSIntegral g α a b w) :
    HasRSIntegral (fun x ↦ f x - g x) α a b (v - w) := by
  simpa only [sub_eq_add_neg] using hasRSIntegral_add hf (hasRSIntegral_neg hg)

/-- Integrators can be added without right continuity. -/
theorem hasRSIntegral_integrator_add (hf : HasRSIntegral f α a b v)
    (hg : HasRSIntegral f β a b w) :
    HasRSIntegral f (fun x ↦ α x + β x) a b (v + w) := by
  refine ⟨?_, hf.2.1, ?_⟩
  · intro x hx y hy hxy
    exact add_le_add (hf.1 hx hy hxy) (hg.1 hx hy hxy)
  · intro ε hε
    obtain ⟨p, hp⟩ := common_control hf hg (ε := ε / 2) (δ := ε / 2)
      (by linarith) (by linarith)
    refine ⟨p, fun q hq tag ht ↦ ?_⟩
    obtain ⟨h₁, h₂⟩ := hp q hq tag ht
    rw [taggedSum_integrator_add]
    have heq : taggedSum q f α tag + taggedSum q f β tag - (v + w) =
        (taggedSum q f α tag - v) + (taggedSum q f β tag - w) := by ring
    rw [heq]
    have := abs_add_le (taggedSum q f α tag - v) (taggedSum q f β tag - w)
    linarith

/-- The scaled integrator must remain monotone; nonnegative scalars suffice. -/
theorem hasRSIntegral_integrator_mul (hf : HasRSIntegral f α a b v)
    {c : ℝ} (hc : 0 ≤ c) :
    HasRSIntegral f (fun x ↦ c * α x) a b (c * v) := by
  refine ⟨fun x hx y hy hxy ↦ mul_le_mul_of_nonneg_left (hf.1 hx hy hxy) hc, hf.2.1, ?_⟩
  intro ε hε
  obtain ⟨p, hp⟩ := hf.2.2 (ε / (|c| + 1)) (div_pos hε (by positivity))
  refine ⟨p, fun q hq tag ht ↦ ?_⟩
  rw [taggedSum_integrator_mul, ← mul_sub]
  exact scaled_error hε (hp q hq tag ht)

/-- Pointwise equality on the closed interval suffices. -/
theorem hasRSIntegral_congr (hf : HasRSIntegral f α a b v)
    (hfg : ∀ x ∈ Icc a b, f x = g x) : HasRSIntegral g α a b v := by
  refine ⟨hf.1, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hf.2.1
    exact ⟨M, fun x hx ↦ by rw [← hfg x hx]; exact hM x hx⟩
  · intro ε hε
    obtain ⟨p, hp⟩ := hf.2.2 ε hε
    refine ⟨p, fun q hq tag ht ↦ ?_⟩
    have heq : taggedSum q g α tag = taggedSum q f α tag := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfg (tag i) (cell_subset q (Finset.mem_range.mp hi) (ht i (Finset.mem_range.mp hi)))]
    rw [heq]
    exact hp q hq tag ht

theorem taggedSum_mono (p : Partition a b) (hα : MonotoneOn α (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) {tag : ℕ → ℝ} (ht : IsTag p tag) :
    taggedSum p f α tag ≤ taggedSum p g α tag := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_right (hfg _ (cell_subset p hi' (ht i hi')))
    (increment_nonneg p hα hi')

/-- Order passes to actual integral values using a common refinement. -/
theorem hasRSIntegral_mono (hf : HasRSIntegral f α a b v) (hg : HasRSIntegral g α a b w)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) : v ≤ w := by
  by_contra hn
  have hgap : 0 < (v - w) / 2 := by linarith
  obtain ⟨p, hp⟩ := common_control hf hg hgap hgap
  obtain ⟨h₁, h₂⟩ := hp p (refines_refl p) p.x (left_isTag p)
  have hmono := taggedSum_mono p hf.1 hfg (left_isTag p)
  have := (abs_lt.mp h₁).1
  have := (abs_lt.mp h₂).2
  linarith

/-- Constants also cover singleton intervals. -/
theorem hasRSIntegral_constant (hab : a ≤ b) (hα : MonotoneOn α (Icc a b)) (c : ℝ) :
    HasRSIntegral (fun _ ↦ c) α a b (c * (α b - α a)) := by
  refine ⟨hα, ⟨|c|, fun _ _ ↦ le_rfl⟩, fun ε hε ↦ ⟨single hab, ?_⟩⟩
  intro q _ tag _
  simpa only [taggedSum_const, sub_self, abs_zero] using hε

theorem hasRSIntegral_nonneg (hf : HasRSIntegral f α a b v)
    (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) : 0 ≤ v := by
  obtain ⟨p, _⟩ := hf.2.2 1 zero_lt_one
  have h := hasRSIntegral_mono (hasRSIntegral_constant (endpoints_le p) hf.1 0) hf hf₀
  simpa only [zero_mul] using h

/-- A bound by a constant gives the total-increment bound. -/
theorem hasRSIntegral_abs_le (hf : HasRSIntegral f α a b v) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) : |v| ≤ M * (α b - α a) := by
  obtain ⟨p, _⟩ := hf.2.2 1 zero_lt_one
  have hl := hasRSIntegral_mono (hasRSIntegral_constant (endpoints_le p) hf.1 (-M)) hf
    (fun x hx ↦ (abs_le.mp (hM x hx)).1)
  have hu := hasRSIntegral_mono hf (hasRSIntegral_constant (endpoints_le p) hf.1 M)
    (fun x hx ↦ (abs_le.mp (hM x hx)).2)
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Domination by an integrable function bounds the absolute integral value.
This does not assume or assert integrability of `|f|`. -/
theorem hasRSIntegral_abs_le_of_abs_le (hf : HasRSIntegral f α a b v)
    (hg : HasRSIntegral g α a b w) (hfg : ∀ x ∈ Icc a b, |f x| ≤ g x) : |v| ≤ w := by
  have hu := hasRSIntegral_mono hf hg (fun x hx ↦ (le_abs_self _).trans (hfg x hx))
  have hl := hasRSIntegral_mono (hasRSIntegral_neg hf) hg
    (fun x hx ↦ (neg_le_abs _).trans (hfg x hx))
  exact abs_le.mpr ⟨by linarith, hu⟩

/-! Darboux versions retain the literal supremum/infimum predicate. -/

theorem hasDarbouxRSIntegral_add (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) (hg : HasDarbouxRSIntegral g α a b w) :
    HasDarbouxRSIntegral (fun x ↦ f x + g x) α a b (v + w) :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab (hasRSIntegral_add
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) (hasRSIntegral_of_hasDarbouxRSIntegral hab hg))

theorem hasDarbouxRSIntegral_mul (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) (c : ℝ) :
    HasDarbouxRSIntegral (fun x ↦ c * f x) α a b (c * v) :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab
    (hasRSIntegral_mul (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) c)

theorem hasDarbouxRSIntegral_neg (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    HasDarbouxRSIntegral (fun x ↦ -f x) α a b (-v) :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab
    (hasRSIntegral_neg (hasRSIntegral_of_hasDarbouxRSIntegral hab hf))

theorem hasDarbouxRSIntegral_sub (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) (hg : HasDarbouxRSIntegral g α a b w) :
    HasDarbouxRSIntegral (fun x ↦ f x - g x) α a b (v - w) :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab (hasRSIntegral_sub
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) (hasRSIntegral_of_hasDarbouxRSIntegral hab hg))

theorem hasDarbouxRSIntegral_integrator_add (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) (hg : HasDarbouxRSIntegral f β a b w) :
    HasDarbouxRSIntegral f (fun x ↦ α x + β x) a b (v + w) :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab (hasRSIntegral_integrator_add
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) (hasRSIntegral_of_hasDarbouxRSIntegral hab hg))

theorem hasDarbouxRSIntegral_integrator_mul (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) {c : ℝ} (hc : 0 ≤ c) :
    HasDarbouxRSIntegral f (fun x ↦ c * α x) a b (c * v) :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab
    (hasRSIntegral_integrator_mul (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) hc)

theorem hasDarbouxRSIntegral_congr (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v)
    (hfg : ∀ x ∈ Icc a b, f x = g x) : HasDarbouxRSIntegral g α a b v :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab
    (hasRSIntegral_congr (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) hfg)

theorem hasDarbouxRSIntegral_mono (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) (hg : HasDarbouxRSIntegral g α a b w)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) : v ≤ w :=
  hasRSIntegral_mono (hasRSIntegral_of_hasDarbouxRSIntegral hab hf)
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hg) hfg

theorem hasDarbouxRSIntegral_nonneg (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v)
    (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) : 0 ≤ v :=
  hasRSIntegral_nonneg (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) hf₀

theorem hasDarbouxRSIntegral_abs_le (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v)
    {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M) : |v| ≤ M * (α b - α a) :=
  hasRSIntegral_abs_le (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) hM

theorem hasDarbouxRSIntegral_abs_le_of_abs_le (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) (hg : HasDarbouxRSIntegral g α a b w)
    (hfg : ∀ x ∈ Icc a b, |f x| ≤ g x) : |v| ≤ w :=
  hasRSIntegral_abs_le_of_abs_le (hasRSIntegral_of_hasDarbouxRSIntegral hab hf)
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hg) hfg

/-- Concatenate two weak partitions, retaining the shared endpoint value. -/
def joinPartition {c : ℝ} (p : Partition a c) (q : Partition c b) : Partition a b where
  n := p.n + q.n
  pos := by have := p.pos; omega
  x := fun i ↦ if i ≤ p.n then p.x i else q.x (i - p.n)
  first := by simp [p.first]
  last := by
    have hn : ¬p.n + q.n ≤ p.n := by have := q.pos; omega
    simp [hn, q.last]
  increasing := by
    intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    dsimp only
    split_ifs with hip hjp
    · exact p.increasing hip hjp hij
    · exact (node_mem p hip).2.trans (node_mem q (by omega)).1
    · omega
    · exact q.increasing (show i - p.n ≤ q.n by omega)
        (show j - p.n ≤ q.n by omega) (Nat.sub_le_sub_right hij p.n)

@[simp] theorem joinPartition_n {c : ℝ} (p : Partition a c) (q : Partition c b) :
    (joinPartition p q).n = p.n + q.n := rfl

theorem joinPartition_prefix {c : ℝ} (p : Partition a c) (q : Partition c b)
    {i : ℕ} (hi : i ≤ p.n) : (joinPartition p q).x i = p.x i := by
  simp only [joinPartition, ite_eq_left hi]

theorem joinPartition_suffix {c : ℝ} (p : Partition a c) (q : Partition c b) (i : ℕ) :
    (joinPartition p q).x (p.n + i) = q.x i := by
  by_cases hi : i = 0
  · subst i
    simp [joinPartition, p.last, q.first]
  · have hn : ¬p.n + i ≤ p.n := by omega
    simp [joinPartition, hn]

/-- Lower sums add exactly, also when a piece is a singleton interval. -/
theorem lowerSum_joinPartition {c : ℝ} (p : Partition a c) (q : Partition c b)
    (f α : ℝ → ℝ) : lowerSum (joinPartition p q) f α = lowerSum p f α + lowerSum q f α := by
  unfold lowerSum
  rw [joinPartition_n, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [joinPartition_prefix p q (by omega), joinPartition_prefix p q (by omega)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [show p.n + i + 1 = p.n + (i + 1) by omega,
      joinPartition_suffix, joinPartition_suffix]

theorem upperSum_joinPartition {c : ℝ} (p : Partition a c) (q : Partition c b)
    (f α : ℝ → ℝ) : upperSum (joinPartition p q) f α = upperSum p f α + upperSum q f α := by
  unfold upperSum
  rw [joinPartition_n, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [joinPartition_prefix p q (by omega), joinPartition_prefix p q (by omega)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [show p.n + i + 1 = p.n + (i + 1) by omega,
      joinPartition_suffix, joinPartition_suffix]

private theorem darboux_of_approximating_sums (hab : a ≤ b)
    (hα : MonotoneOn α (Icc a b)) {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hs : ∀ ε > (0 : ℝ), ∃ p : Partition a b,
      v - ε < lowerSum p f α ∧ upperSum p f α < v + ε) :
    HasDarbouxRSIntegral f α a b v := by
  let L := sSup (Set.range fun p : Partition a b ↦ lowerSum p f α)
  let U := sInf (Set.range fun p : Partition a b ↦ upperSum p f α)
  have hLU : L ≤ U := lowerIntegral_le_upperIntegral hab hα hM
  have hvL : v ≤ L := by
    by_contra hn
    obtain ⟨p, hp, _⟩ := hs (v - L) (by linarith)
    have : lowerSum p f α ≤ L := le_csSup (lowerSum_range_bounded hα hM).2 ⟨p, rfl⟩
    linarith
  have hUv : U ≤ v := by
    by_contra hn
    obtain ⟨p, _, hp⟩ := hs (U - v) (by linarith)
    have : U ≤ upperSum p f α := csInf_le (upperSum_range_bounded hα hM).1 ⟨p, rfl⟩
    linarith
  exact ⟨hα, ⟨M, hM⟩, le_antisymm (hLU.trans hUv) hvL,
    le_antisymm hUv (hvL.trans hLU)⟩

/-- Integral additivity across a cut, assuming genuine integrability on each piece.
The integrator need not be continuous at the cut. -/
theorem hasDarbouxRSIntegral_join {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : HasDarbouxRSIntegral f α a c v) (hg : HasDarbouxRSIntegral f α c b w) :
    HasDarbouxRSIntegral f α a b (v + w) := by
  have hα : MonotoneOn α (Icc a b) := by
    intro x hx y hy hxy
    by_cases hxc : x ≤ c
    · by_cases hyc : y ≤ c
      · exact hf.1 ⟨hx.1, hxc⟩ ⟨hy.1, hyc⟩ hxy
      · exact (hf.1 ⟨hx.1, hxc⟩ ⟨hac, le_rfl⟩ hxc).trans
          (hg.1 ⟨le_rfl, hcb⟩ ⟨le_of_not_ge hyc, hy.2⟩ (le_of_not_ge hyc))
    · exact hg.1 ⟨le_of_not_ge hxc, hx.2⟩
        ⟨(le_of_not_ge hxc).trans hxy, hy.2⟩ hxy
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨N, hN⟩ := hg.2.1
  have hbound : ∀ x ∈ Icc a b, |f x| ≤ max M N := by
    intro x hx
    by_cases hxc : x ≤ c
    · exact (hM x ⟨hx.1, hxc⟩).trans (le_max_left _ _)
    · exact (hN x ⟨le_of_not_ge hxc, hx.2⟩).trans (le_max_right _ _)
  apply darboux_of_approximating_sums (hac.trans hcb) hα hbound
  intro ε hε
  obtain ⟨p, hp₁, hp₂⟩ := hasRSIntegral_small_darboux_sums
    (hasRSIntegral_of_hasDarbouxRSIntegral hac hf) (show 0 < ε / 2 by linarith)
  obtain ⟨q, hq₁, hq₂⟩ := hasRSIntegral_small_darboux_sums
    (hasRSIntegral_of_hasDarbouxRSIntegral hcb hg) (show 0 < ε / 2 by linarith)
  refine ⟨joinPartition p q, ?_, ?_⟩
  · rw [lowerSum_joinPartition]; linarith
  · rw [upperSum_joinPartition]; linarith

theorem hasRSIntegral_join {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : HasRSIntegral f α a c v) (hg : HasRSIntegral f α c b w) :
    HasRSIntegral f α a b (v + w) :=
  hasRSIntegral_of_hasDarbouxRSIntegral (hac.trans hcb) (hasDarbouxRSIntegral_join hac hcb
    (hasDarbouxRSIntegral_of_hasRSIntegral hac hf) (hasDarbouxRSIntegral_of_hasRSIntegral hcb hg))

/-- The Darboux small-gap criterion constructs a value; convergence is not assumed. -/
theorem exists_hasDarbouxRSIntegral_of_small_gap (hab : a ≤ b)
    (hα : MonotoneOn α (Icc a b)) {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hgap : ∀ ε > (0 : ℝ), ∃ p : Partition a b,
      upperSum p f α - lowerSum p f α < ε) :
    ∃ value : ℝ, HasDarbouxRSIntegral f α a b value := by
  let L := sSup (Set.range fun p : Partition a b ↦ lowerSum p f α)
  let U := sInf (Set.range fun p : Partition a b ↦ upperSum p f α)
  have hLU : L ≤ U := lowerIntegral_le_upperIntegral hab hα hM
  have hUL : U ≤ L := by
    by_contra hn
    obtain ⟨p, hp⟩ := hgap (U - L) (by linarith)
    have hl : lowerSum p f α ≤ L := le_csSup (lowerSum_range_bounded hα hM).2 ⟨p, rfl⟩
    have hu : U ≤ upperSum p f α := csInf_le (upperSum_range_bounded hα hM).1 ⟨p, rfl⟩
    linarith
  exact ⟨L, hα, ⟨M, hM⟩, rfl, le_antisymm hUL hLU⟩

/-- Taking absolute values cannot increase a Darboux gap. -/
theorem darboux_gap_abs_le (p : Partition a b) (hα : MonotoneOn α (Icc a b))
    {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M) :
    upperSum p (fun x ↦ |f x|) α - lowerSum p (fun x ↦ |f x|) α ≤
      upperSum p f α - lowerSum p f α := by
  unfold upperSum lowerSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  let s := Icc (p.x i) (p.x (i + 1))
  have hs : s.Nonempty := ⟨p.x i, left_isTag p i hi'⟩
  have hb : BddBelow (f '' s) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset p hi' hx))).1
  have ha : BddAbove (f '' s) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset p hi' hx))).2
  have hosc : ∀ x ∈ s, ∀ y ∈ s,
      |f x| - |f y| ≤ sSup (f '' s) - sInf (f '' s) := by
    intro x hx y hy
    have hfxl := csInf_le hb (mem_image_of_mem f hx)
    have hfyl := csInf_le hb (mem_image_of_mem f hy)
    have hfxu := le_csSup ha (mem_image_of_mem f hx)
    have hfyu := le_csSup ha (mem_image_of_mem f hy)
    have hdist : |f x - f y| ≤ sSup (f '' s) - sInf (f '' s) := by
      apply abs_le.mpr
      constructor <;> linarith
    exact (abs_sub_abs_le_abs_sub _ _).trans hdist
  have hcell : sSup ((fun x ↦ |f x|) '' s) - sInf ((fun x ↦ |f x|) '' s) ≤
      sSup (f '' s) - sInf (f '' s) := by
    rw [sub_le_iff_le_add]
    apply csSup_le (hs.image _)
    rintro _ ⟨x, hx, rfl⟩
    have hl : |f x| - (sSup (f '' s) - sInf (f '' s)) ≤
        sInf ((fun x ↦ |f x|) '' s) := by
      apply le_csInf (hs.image _)
      rintro _ ⟨y, hy, rfl⟩
      linarith [hosc x hx y hy]
    linarith
  simpa only [← sub_mul] using
    mul_le_mul_of_nonneg_right hcell (increment_nonneg p hα hi')

/-- Absolute-value integrability is proved, rather than added as a hypothesis. -/
theorem exists_hasDarbouxRSIntegral_abs (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ value : ℝ, HasDarbouxRSIntegral (fun x ↦ |f x|) α a b value := by
  obtain ⟨M, hM⟩ := hf.2.1
  apply exists_hasDarbouxRSIntegral_of_small_gap hab hf.1
    (show ∀ x ∈ Icc a b, |(|f x|)| ≤ M by simpa only [abs_abs] using hM)
  intro ε hε
  obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) (show 0 < ε / 2 by linarith)
  exact ⟨p, (darboux_gap_abs_le p hf.1 hM).trans_lt (by linarith)⟩

theorem exists_hasRSIntegral_abs (hf : HasRSIntegral f α a b v) :
    ∃ value : ℝ, HasRSIntegral (fun x ↦ |f x|) α a b value := by
  obtain ⟨p, _⟩ := hf.2.2 1 zero_lt_one
  have hab := endpoints_le p
  obtain ⟨value, hv⟩ := exists_hasDarbouxRSIntegral_abs hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hf)
  exact ⟨value, hasRSIntegral_of_hasDarbouxRSIntegral hab hv⟩

/-- The absolute integral exists and bounds the absolute integral value. -/
theorem hasDarbouxRSIntegral_abs_bound (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ value : ℝ, HasDarbouxRSIntegral (fun x ↦ |f x|) α a b value ∧ |v| ≤ value := by
  obtain ⟨value, hv⟩ := exists_hasDarbouxRSIntegral_abs hab hf
  exact ⟨value, hv, hasDarbouxRSIntegral_abs_le_of_abs_le hab hf hv (fun _ _ ↦ le_rfl)⟩

theorem hasRSIntegral_abs_bound (hf : HasRSIntegral f α a b v) :
    ∃ value : ℝ, HasRSIntegral (fun x ↦ |f x|) α a b value ∧ |v| ≤ value := by
  obtain ⟨value, hv⟩ := exists_hasRSIntegral_abs hf
  exact ⟨value, hv, hasRSIntegral_abs_le_of_abs_le hf hv (fun _ _ ↦ le_rfl)⟩

/-- Every bounded integrand has integral zero when the raw total increment is zero. -/
theorem hasRSIntegral_zero_mass (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (hmass : α b = α a) :
    HasRSIntegral f α a b 0 := by
  refine ⟨hα, ⟨M, hM⟩, fun ε hε ↦ ⟨single hab, fun q _ tag ht ↦ ?_⟩⟩
  have h := abs_taggedSum_le q hα hM ht
  rw [hmass, sub_self, mul_zero] at h
  simpa only [sub_zero] using h.trans_lt hε

theorem hasDarbouxRSIntegral_zero_mass (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (hmass : α b = α a) :
    HasDarbouxRSIntegral f α a b 0 :=
  hasDarbouxRSIntegral_of_hasRSIntegral hab (hasRSIntegral_zero_mass hab hα hM hmass)

/-- The node set of a concatenation is the union, without discarding repeated cells. -/
theorem joinPartition_nodes {c : ℝ} (p : Partition a c) (q : Partition c b) :
    (joinPartition p q).x '' Iic (joinPartition p q).n =
      (p.x '' Iic p.n) ∪ (q.x '' Iic q.n) := by
  ext z
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hip : i ≤ p.n
    · exact Or.inl ⟨i, hip, joinPartition_prefix p q hip |>.symm⟩
    · apply Or.inr
      refine ⟨i - p.n, show i - p.n ≤ q.n by change i ≤ p.n + q.n at hi; omega, ?_⟩
      rw [← joinPartition_suffix p q (i - p.n)]
      congr 1
      omega
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, show i ≤ p.n + q.n by change i ≤ p.n at hi; omega,
        joinPartition_prefix p q hi⟩
    · exact ⟨p.n + i, show p.n + i ≤ p.n + q.n from Nat.add_le_add_left hi _,
        joinPartition_suffix p q i⟩

/-- Cut a partition by filtering its vertices and inserting the cut point.
Both pieces remain nonempty partitions when the cut is an endpoint. -/
noncomputable def cutLeft (p : Partition a b) {c : ℝ} (hac : a ≤ c) (_hcb : c ≤ b) :
    Partition a c := by
  classical
  exact ofVertices ((vertices p).filter (fun x ↦ x ≤ c) ∪ {c})
    (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨(mem_vertices p a).mpr ⟨0, by simp, p.first⟩, hac⟩))
    (Finset.mem_union_right _ (Finset.mem_singleton_self c)) (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hv, hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, hi, rfl⟩ := (mem_vertices p x).mp hv
        exact ⟨(node_mem p hi).1, hxc⟩
      · have : x = c := Finset.mem_singleton.mp hx
        subst x
        exact ⟨hac, le_rfl⟩)

noncomputable def cutRight (p : Partition a b) {c : ℝ} (_hac : a ≤ c) (hcb : c ≤ b) :
    Partition c b := by
  classical
  exact ofVertices ((vertices p).filter (fun x ↦ c ≤ x) ∪ {c})
    (Finset.mem_union_right _ (Finset.mem_singleton_self c))
    (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨(mem_vertices p b).mpr ⟨p.n, by simp, p.last⟩, hcb⟩)) (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hv, hcx⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, hi, rfl⟩ := (mem_vertices p x).mp hv
        exact ⟨hcx, (node_mem p hi).2⟩
      · have : x = c := Finset.mem_singleton.mp hx
        subst x
        exact ⟨le_rfl, hcb⟩)

/-- Cutting and rejoining is a genuine refinement of the original partition. -/
theorem cut_join_refines (p : Partition a b) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    Refines (joinPartition (cutLeft p hac hcb) (cutRight p hac hcb)) p := by
  classical
  intro z hz
  rw [joinPartition_nodes]
  by_cases hzc : z ≤ c
  · apply Or.inl
    rw [cutLeft, ofVertices_nodes]
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(mem_vertices p z).mpr hz, hzc⟩)
  · apply Or.inr
    rw [cutRight, ofVertices_nodes]
    exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨(mem_vertices p z).mpr hz, le_of_not_ge hzc⟩)

/-- Each restricted gap is bounded by the original gap. -/
theorem cut_gaps_le (p : Partition a b) {c M : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hα : MonotoneOn α (Icc a b)) (hM : ∀ x ∈ Icc a b, |f x| ≤ M) :
    (upperSum (cutLeft p hac hcb) f α - lowerSum (cutLeft p hac hcb) f α ≤
      upperSum p f α - lowerSum p f α) ∧
    (upperSum (cutRight p hac hcb) f α - lowerSum (cutRight p hac hcb) f α ≤
      upperSum p f α - lowerSum p f α) := by
  have hleft : Icc a c ⊆ Icc a b := fun _ hx ↦ ⟨hx.1, hx.2.trans hcb⟩
  have hright : Icc c b ⊆ Icc a b := fun _ hx ↦ ⟨hac.trans hx.1, hx.2⟩
  have hl := lowerSum_le_upperSum (cutLeft p hac hcb) (hα.mono hleft)
    (fun x hx ↦ hM x (hleft hx))
  have hr := lowerSum_le_upperSum (cutRight p hac hcb) (hα.mono hright)
    (fun x hx ↦ hM x (hright hx))
  have hlow := lowerSum_mono_refinement (cut_join_refines p hac hcb) hα hM
  have hupp := upperSum_anti_refinement (cut_join_refines p hac hcb) hα hM
  rw [lowerSum_joinPartition] at hlow
  rw [upperSum_joinPartition] at hupp
  constructor <;> linarith

/-- Full interval splitting, with integrability on both pieces proved.
No continuity at the cut is needed, and both endpoint cuts are allowed. -/
theorem hasDarbouxRSIntegral_split {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ left right : ℝ, HasDarbouxRSIntegral f α a c left ∧
      HasDarbouxRSIntegral f α c b right ∧ left + right = v := by
  obtain ⟨M, hM⟩ := hf.2.1
  have hleft : Icc a c ⊆ Icc a b := fun _ hx ↦ ⟨hx.1, hx.2.trans hcb⟩
  have hright : Icc c b ⊆ Icc a b := fun _ hx ↦ ⟨hac.trans hx.1, hx.2⟩
  have hsmall : ∀ ε > (0 : ℝ), ∃ p : Partition a b,
      upperSum p f α - lowerSum p f α < ε := by
    intro ε hε
    obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
      (hasRSIntegral_of_hasDarbouxRSIntegral (hac.trans hcb) hf)
      (show 0 < ε / 2 by linarith)
    exact ⟨p, by linarith⟩
  obtain ⟨left, hl⟩ := exists_hasDarbouxRSIntegral_of_small_gap hac (hf.1.mono hleft)
    (fun x hx ↦ hM x (hleft hx)) (by
      intro ε hε
      obtain ⟨p, hp⟩ := hsmall ε hε
      exact ⟨cutLeft p hac hcb, ((cut_gaps_le p hac hcb hf.1 hM).1).trans_lt hp⟩)
  obtain ⟨right, hr⟩ := exists_hasDarbouxRSIntegral_of_small_gap hcb (hf.1.mono hright)
    (fun x hx ↦ hM x (hright hx)) (by
      intro ε hε
      obtain ⟨p, hp⟩ := hsmall ε hε
      exact ⟨cutRight p hac hcb, ((cut_gaps_le p hac hcb hf.1 hM).2).trans_lt hp⟩)
  refine ⟨left, right, hl, hr, ?_⟩
  exact hasRSIntegral_unique
    (hasRSIntegral_of_hasDarbouxRSIntegral (hac.trans hcb) (hasDarbouxRSIntegral_join hac hcb hl hr))
    (hasRSIntegral_of_hasDarbouxRSIntegral (hac.trans hcb) hf)

theorem hasRSIntegral_split {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : HasRSIntegral f α a b v) :
    ∃ left right : ℝ, HasRSIntegral f α a c left ∧
      HasRSIntegral f α c b right ∧ left + right = v := by
  obtain ⟨left, right, hl, hr, hv⟩ := hasDarbouxRSIntegral_split hac hcb
    (hasDarbouxRSIntegral_of_hasRSIntegral (hac.trans hcb) hf)
  exact ⟨left, right, hasRSIntegral_of_hasDarbouxRSIntegral hac hl,
    hasRSIntegral_of_hasDarbouxRSIntegral hcb hr, hv⟩

/-! Regression checks: raw jumps, zero mass, negative and zero scalars,
repeated cells, and endpoint cuts. These are not exercise completions. -/

example : HasDarbouxRSIntegral (fun _ ↦ (-6 : ℝ)) delayedStep (-1) 1 (-6) := by
  have h := hasRSIntegral_constant (by norm_num : (-1 : ℝ) ≤ 1)
    (monotone_delayedStep.monotoneOn _) 2
  have hm := hasRSIntegral_mul h (-3)
  exact hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num) (by norm_num [delayedStep] at hm; exact hm)

example (hf : HasRSIntegral f α a b v) :
    HasRSIntegral (fun _ ↦ 0) α a b 0 := by
  simpa only [zero_mul] using hasRSIntegral_mul hf 0

-- The jump at the cut belongs to the right-hand increment for this raw integrator.
example : HasDarbouxRSIntegral (fun _ ↦ (2 : ℝ)) delayedStep (-1) 1 2 := by
  have hl := hasRSIntegral_constant (by norm_num : (-1 : ℝ) ≤ 0)
    (monotone_delayedStep.monotoneOn _) 2
  have hr := hasRSIntegral_constant (by norm_num : (0 : ℝ) ≤ 1)
    (monotone_delayedStep.monotoneOn _) 2
  have hj := hasRSIntegral_join (by norm_num : (-1 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1) hl hr
  exact hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num) (by norm_num [delayedStep] at hj; exact hj)

example : HasDarbouxRSIntegral (fun _ ↦ (2 : ℝ))
    (fun x ↦ delayedStep x + delayedStep x) (-1) 1 4 := by
  have h := hasRSIntegral_constant (by norm_num : (-1 : ℝ) ≤ 1)
    (monotone_delayedStep.monotoneOn _) 2
  have hadd := hasRSIntegral_integrator_add h h
  exact hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num) (by norm_num [delayedStep] at hadd ⊢; exact hadd)

-- A discontinuous integrand and a raw integrator with a jump immediately after b.
example : HasDarbouxRSIntegral (fun x ↦ if x = (-1 : ℝ) then 3 else -2)
    delayedStep (-1) 0 0 := by
  apply hasDarbouxRSIntegral_zero_mass (by norm_num)
    (monotone_delayedStep.monotoneOn _) (M := 3)
  · intro x _
    split_ifs <;> norm_num
  · norm_num [delayedStep]

example (f α : ℝ → ℝ) (a : ℝ) :
    (joinPartition (degenerate a) (degenerate a)).n = 2 ∧
      lowerSum (joinPartition (degenerate a) (degenerate a)) f α = 0 ∧
      upperSum (joinPartition (degenerate a) (degenerate a)) f α = 0 := by
  exact ⟨rfl, lowerSum_self _ _ _, upperSum_self _ _ _⟩

example (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ left right : ℝ, HasDarbouxRSIntegral f α a a left ∧
      HasDarbouxRSIntegral f α a b right ∧ left + right = v :=
  hasDarbouxRSIntegral_split le_rfl hab hf

example (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ left right : ℝ, HasDarbouxRSIntegral f α a b left ∧
      HasDarbouxRSIntegral f α b b right ∧ left + right = v :=
  hasDarbouxRSIntegral_split hab le_rfl hf

end Rudin.Support.StieltjesIntegralLaws
