module

public import Math.Rudin.Support.StieltjesIntegralLaws

/-!
# R06E03: the three raw step integrators

Source: Rudin, Third Edition, book page 138 (PDF page 147).
All sums use the printed values at zero. Boundedness is the source hypothesis;
no continuity away from zero is required.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
  Rudin.Support.StieltjesEquivalence Rudin.Support.StieltjesIntegralLaws

/-- A raw unit jump with specified value at zero. -/
noncomputable def jumpBeta (c x : ℝ) : ℝ := if x < 0 then 0 else if x = 0 then c else 1

/-- The source's first integrator, with value zero at zero. -/
noncomputable def beta1 : ℝ → ℝ := jumpBeta 0
/-- The source's second integrator, with value one at zero. -/
noncomputable def beta2 : ℝ → ℝ := jumpBeta 1
/-- The source's third integrator, with value one half at zero. -/
noncomputable def beta3 : ℝ → ℝ := jumpBeta (1 / 2)

private theorem beta_mono {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1) :
    Monotone (jumpBeta c) := by
  intro x y hxy
  unfold jumpBeta
  split_ifs <;> try linarith
  exfalso
  have hx : x = 0 := by linarith
  contradiction

private theorem beta_support {c s t : ℝ} (hst : s ≤ t)
    (hne : jumpBeta c t - jumpBeta c s ≠ 0) : 0 ∈ Icc s t := by
  constructor
  · by_contra h
    have hs : 0 < s := lt_of_not_ge h
    have ht : 0 < t := hs.trans_le hst
    simp [jumpBeta, not_lt.mpr hs.le, not_lt.mpr ht.le, hs.ne', ht.ne'] at hne
  · by_contra h
    have ht : t < 0 := lt_of_not_ge h
    have hs : s < 0 := hst.trans_lt ht
    simp [jumpBeta, hs, ht] at hne

/-- A used partition vertex cannot be strictly inside a cell. Repeated nodes
are allowed. -/
private theorem vertex_outside_cell {a b z : ℝ} (p : Partition a b)
    (hz : z ∈ p.x '' Iic p.n) {i : ℕ} (hi : i < p.n) :
    z ≤ p.x i ∨ p.x (i + 1) ≤ z := by
  obtain ⟨j, hj, rfl⟩ := hz
  change j ≤ p.n at hj
  by_cases hji : j ≤ i
  · exact Or.inl (p.increasing hj (show i ≤ p.n by omega) hji)
  · exact Or.inr (p.increasing (show i + 1 ≤ p.n by omega) hj (by omega))

/-- Tags at zero in every cell that contains zero. -/
private noncomputable def zeroTags (p : Partition (-1) 1) (i : ℕ) : ℝ :=
  if 0 ∈ Icc (p.x i) (p.x (i + 1)) then 0 else p.x i

private theorem zeroTags_valid (p : Partition (-1) 1) : IsTag p (zeroTags p) := by
  intro i hi
  unfold zeroTags
  split_ifs with h
  · exact h
  · exact left_isTag p i hi

/-- All increments not incident with zero vanish. Thus these tags give exactly
`f 0`, for every raw choice of the value at zero. -/
private theorem zeroTags_sum (p : Partition (-1) 1) (f : ℝ → ℝ) (c : ℝ) :
    taggedSum p f (jumpBeta c) (zeroTags p) = f 0 := by
  calc
    _ = taggedSum p (fun _ => f 0) (jumpBeta c) (zeroTags p) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : jumpBeta c (p.x (i + 1)) - jumpBeta c (p.x i) = 0
      · simp [h]
      · have hz := beta_support (left_isTag p i (Finset.mem_range.mp hi)).2 h
        simp [zeroTags, hz]
    _ = f 0 := by simp [taggedSum_const, jumpBeta]

private theorem modified_sum (p : Partition (-1) 1) (f : ℝ → ℝ) (c : ℝ)
    {i : ℕ} (hi : i < p.n) (hz : 0 ∈ Icc (p.x i) (p.x (i + 1))) (y : ℝ) :
    taggedSum p f (jumpBeta c) (Function.update (zeroTags p) i y) =
      f 0 + (f y - f 0) * (jumpBeta c (p.x (i + 1)) - jumpBeta c (p.x i)) := by
  classical
  have hs : taggedSum p f (jumpBeta c) (Function.update (zeroTags p) i y) -
      taggedSum p f (jumpBeta c) (zeroTags p) =
      (f y - f 0) * (jumpBeta c (p.x (i + 1)) - jumpBeta c (p.x i)) := by
    rw [taggedSum, taggedSum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp [zeroTags, hz, sub_mul]
    · intro j hj hji
      simp [Function.update_of_ne hji]
    · intro hn
      exact (hn (Finset.mem_range.mpr hi)).elim
  rw [zeroTags_sum] at hs
  linarith

private theorem beta_integral_value {f : ℝ → ℝ} {c v : ℝ}
    (h : HasRSIntegral f (jumpBeta c) (-1) 1 v) : v = f 0 := by
  by_contra hn
  obtain ⟨p, hp⟩ := h.2.2 |f 0 - v| (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hn)))
  have he := hp p (refines_refl p) (zeroTags p) (zeroTags_valid p)
  rw [zeroTags_sum] at he
  exact (lt_irrefl _ he)

private theorem beta_cell_control {f : ℝ → ℝ} {c v ε : ℝ}
    (h : HasRSIntegral f (jumpBeta c) (-1) 1 v) (hε : 0 < ε) :
    ∃ p : Partition (-1) 1, ∀ i < p.n,
      0 ∈ Icc (p.x i) (p.x (i + 1)) →
      ∀ y ∈ Icc (p.x i) (p.x (i + 1)),
      |f y - f 0| * |jumpBeta c (p.x (i + 1)) - jumpBeta c (p.x i)| < ε := by
  classical
  obtain ⟨p, hp⟩ := h.2.2 ε hε
  refine ⟨p, fun i hi hz y hy => ?_⟩
  have ht : IsTag p (Function.update (zeroTags p) i y) := by
    intro j hj
    by_cases he : j = i
    · subst j; simpa using hy
    · simpa [Function.update_of_ne he] using zeroTags_valid p j hj
  have he := hp p (refines_refl p) _ ht
  rw [modified_sum p f c hi hz y, beta_integral_value h] at he
  simpa only [add_sub_cancel_left, abs_mul] using he

/-- Locate the first node where a monotone predicate becomes true. -/
private theorem crossing {a b : ℝ} (p : Partition a b) (P : ℝ → Prop)
    [DecidablePred P] (ha : ¬ P a) (hb : P b) :
    ∃ i < p.n, ¬ P (p.x i) ∧ P (p.x (i + 1)) := by
  have hex : ∃ j, j ≤ p.n ∧ P (p.x j) := ⟨p.n, le_rfl, by simpa [p.last]⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    have hp : P (p.x 0) := he ▸ hk.2
    exact ha (p.first ▸ hp)
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · exact fun h => (Nat.find_min hex (show k - 1 < k by omega)) ⟨by omega, h⟩
  · simpa only [Nat.sub_add_cancel hk0] using hk.2

private theorem beta_right_necessary {f : ℝ → ℝ} {c v : ℝ}
    (hc : 0 ≤ c) (hc' : c < 1)
    (h : HasRSIntegral f (jumpBeta c) (-1) 1 v) :
    ContinuousWithinAt f (Ici 0) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := beta_cell_control h (mul_pos hε (sub_pos.mpr hc'))
  obtain ⟨i, hi, hs, ht⟩ := crossing p (fun x : ℝ => 0 < x) (by norm_num) (by norm_num)
  have hs' : p.x i ≤ 0 := le_of_not_gt hs
  refine ⟨p.x (i + 1), ht, fun y hy hyd => ?_⟩
  have hy' : y < p.x (i + 1) := by simpa [Real.dist_eq, abs_of_nonneg hy] using hyd
  have he := hp i hi ⟨hs', ht.le⟩ y ⟨hs'.trans hy, hy'.le⟩
  have hd : 1 - c ≤ |jumpBeta c (p.x (i + 1)) - jumpBeta c (p.x i)| := by
    have hr : jumpBeta c (p.x (i + 1)) = 1 := by
      simp [jumpBeta, not_lt.mpr ht.le, ht.ne']
    rw [hr]
    rcases lt_or_eq_of_le hs' with hl | hl
    · simp [jumpBeta, hl, hc]
    · simp [hl, jumpBeta, abs_of_nonneg (sub_nonneg.mpr hc'.le)]
  rw [Real.dist_eq]
  have hn := mul_le_mul_of_nonneg_left hd (abs_nonneg (f y - f 0))
  exact (mul_lt_mul_iff_left₀ (sub_pos.mpr hc')).mp (hn.trans_lt he)

private theorem beta_left_necessary {f : ℝ → ℝ} {c v : ℝ}
    (hc : 0 < c) (hc' : c ≤ 1)
    (h : HasRSIntegral f (jumpBeta c) (-1) 1 v) :
    ContinuousWithinAt f (Iic 0) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := beta_cell_control h (mul_pos hε hc)
  obtain ⟨i, hi, hs, ht⟩ := crossing p (fun x : ℝ => 0 ≤ x) (by norm_num) (by norm_num)
  have hs' : p.x i < 0 := lt_of_not_ge hs
  refine ⟨-p.x i, by linarith, fun y hy hyd => ?_⟩
  have hy' : p.x i < y := by
    have hd : -y < -p.x i := by simpa [Real.dist_eq, abs_of_nonpos hy] using hyd
    linarith
  have he := hp i hi ⟨hs'.le, ht⟩ y ⟨hy'.le, hy.trans ht⟩
  have hd : c ≤ |jumpBeta c (p.x (i + 1)) - jumpBeta c (p.x i)| := by
    rw [show jumpBeta c (p.x i) = 0 by simp [jumpBeta, hs'], sub_zero]
    rcases lt_or_eq_of_le ht with hr | hr
    · simp [jumpBeta, not_lt.mpr hr.le, hr.ne', hc']
    · simp [← hr, jumpBeta, abs_of_nonneg hc.le]
  rw [Real.dist_eq]
  have hn := mul_le_mul_of_nonneg_left hd (abs_nonneg (f y - f 0))
  exact (mul_lt_mul_iff_left₀ hc).mp (hn.trans_lt he)

private noncomputable def localPartition (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    Partition (-1) 1 :=
  ofVertices {-1, -d, 0, d, 1} (by simp) (by simp) (by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> constructor <;> linarith)

private theorem localPartition_vertex (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    {z : ℝ} (hz : z = -d ∨ z = 0 ∨ z = d) :
    z ∈ (localPartition d hd hd1).x '' Iic (localPartition d hd hd1).n := by
  rw [localPartition, ofVertices_nodes]
  rcases hz with rfl | rfl | rfl <;> simp

private theorem beta_zero_nonpos {x : ℝ} (hx : x ≤ 0) : jumpBeta 0 x = 0 := by
  rcases lt_or_eq_of_le hx with h | rfl <;> simp [jumpBeta, *]

private theorem beta_one_nonneg {x : ℝ} (hx : 0 ≤ x) : jumpBeta 1 x = 1 := by
  simp [jumpBeta, not_lt.mpr hx]

/-- A partition with vertices on both sides of zero localizes every nonzero
increment. A zero coefficient does not require continuity on that side. -/
private theorem beta_sufficient {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M)
    (hr : c < 1 → ContinuousWithinAt f (Ici 0) 0)
    (hl : 0 < c → ContinuousWithinAt f (Iic 0) 0) :
    HasRSIntegral f (jumpBeta c) (-1) 1 (f 0) := by
  refine ⟨(beta_mono hc hc').monotoneOn _, hb, fun ε hε => ?_⟩
  obtain ⟨δr, hδr, hright⟩ : ∃ δ > (0 : ℝ), ∀ y ∈ Ici (0 : ℝ),
      dist y 0 < δ → c < 1 → dist (f y) (f 0) < ε / 2 := by
    by_cases h : c < 1
    · obtain ⟨δ, hδ, hm⟩ := Metric.continuousWithinAt_iff.mp (hr h) (ε / 2) (by linarith)
      exact ⟨δ, hδ, fun y hy hd _ => hm hy hd⟩
    · exact ⟨1, zero_lt_one, fun _ _ _ h' => (h h').elim⟩
  obtain ⟨δl, hδl, hleft⟩ : ∃ δ > (0 : ℝ), ∀ y ∈ Iic (0 : ℝ),
      dist y 0 < δ → 0 < c → dist (f y) (f 0) < ε / 2 := by
    by_cases h : 0 < c
    · obtain ⟨δ, hδ, hm⟩ := Metric.continuousWithinAt_iff.mp (hl h) (ε / 2) (by linarith)
      exact ⟨δ, hδ, fun y hy hd _ => hm hy hd⟩
    · exact ⟨1, zero_lt_one, fun _ _ _ h' => (h h').elim⟩
  let d : ℝ := min (1 / 2) (min δr δl / 2)
  have hd : 0 < d := lt_min (by norm_num) (div_pos (lt_min hδr hδl) (by norm_num))
  have hd1 : d ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hdr : d < δr := by
    have := min_le_right (1 / 2 : ℝ) (min δr δl / 2)
    have := min_le_left δr δl
    dsimp [d]
    linarith
  have hdl : d < δl := by
    have := min_le_right (1 / 2 : ℝ) (min δr δl / 2)
    have := min_le_right δr δl
    dsimp [d]
    linarith
  refine ⟨localPartition d hd hd1, fun q hq tag ht => ?_⟩
  have hv (z : ℝ) (hz : z = -d ∨ z = 0 ∨ z = d) :
      z ∈ q.x '' Iic q.n := hq (localPartition_vertex d hd hd1 hz)
  have herr : ∀ i < q.n,
      |f (tag i) - f 0| * (jumpBeta c (q.x (i + 1)) - jumpBeta c (q.x i)) ≤
        (ε / 2) * (jumpBeta c (q.x (i + 1)) - jumpBeta c (q.x i)) := by
    intro i hi
    by_cases hn : jumpBeta c (q.x (i + 1)) - jumpBeta c (q.x i) = 0
    · simp [hn]
    have h0 := beta_support (left_isTag q i hi).2 hn
    have hlo : -d ≤ q.x i := by
      rcases vertex_outside_cell q (hv (-d) (Or.inl rfl)) hi with h | h
      · exact h
      · linarith [h0.2]
    have hhi : q.x (i + 1) ≤ d := by
      rcases vertex_outside_cell q (hv d (Or.inr (Or.inr rfl))) hi with h | h
      · linarith [h0.1]
      · exact h
    have hy := ht i hi
    have hylo : -d ≤ tag i := hlo.trans hy.1
    have hyhi : tag i ≤ d := hy.2.trans hhi
    have hclose : |f (tag i) - f 0| ≤ ε / 2 := by
      rcases lt_trichotomy (tag i) 0 with hyneg | hyzero | hypos
      · have hright0 : q.x (i + 1) ≤ 0 := by
          rcases vertex_outside_cell q (hv 0 (Or.inr (Or.inl rfl))) hi with h | h
          · linarith [hy.1]
          · exact h
        have hcpos : 0 < c := by
          by_contra h
          have he : c = 0 := le_antisymm (le_of_not_gt h) hc
          rw [he, beta_zero_nonpos hright0,
            beta_zero_nonpos (h0.1), sub_self] at hn
          exact hn rfl
        have hdist : dist (tag i) 0 < δl := by
          rw [Real.dist_eq, sub_zero, abs_of_neg hyneg]
          linarith
        simpa [Real.dist_eq] using (hleft (tag i) hyneg.le hdist hcpos).le
      · simp only [hyzero, sub_self, abs_zero]
        linarith
      · have hleft0 : 0 ≤ q.x i := by
          rcases vertex_outside_cell q (hv 0 (Or.inr (Or.inl rfl))) hi with h | h
          · exact h
          · linarith [hy.2]
        have hclt : c < 1 := by
          by_contra h
          have he : c = 1 := le_antisymm hc' (le_of_not_gt h)
          rw [he, beta_one_nonneg (h0.2), beta_one_nonneg hleft0, sub_self] at hn
          exact hn rfl
        have hdist : dist (tag i) 0 < δr := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hypos]
          exact hyhi.trans_lt hdr
        simpa [Real.dist_eq] using (hright (tag i) hypos.le hdist hclt).le
    exact mul_le_mul_of_nonneg_right hclose
      (increment_nonneg q ((beta_mono hc hc').monotoneOn _) hi)
  have hsum : taggedSum q f (jumpBeta c) tag - f 0 =
      ∑ i ∈ Finset.range q.n,
        (f (tag i) - f 0) * (jumpBeta c (q.x (i + 1)) - jumpBeta c (q.x i)) := by
    calc
      _ = taggedSum q f (jumpBeta c) tag -
          taggedSum q (fun _ => f 0) (jumpBeta c) tag := by
        simp [taggedSum_const, jumpBeta]
      _ = _ := by simp [taggedSum, sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ Finset.range q.n,
        |(f (tag i) - f 0) * (jumpBeta c (q.x (i + 1)) - jumpBeta c (q.x i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range q.n,
        (ε / 2) * (jumpBeta c (q.x (i + 1)) - jumpBeta c (q.x i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (increment_nonneg q ((beta_mono hc hc').monotoneOn _)
        (Finset.mem_range.mp hi))]
      exact herr i (Finset.mem_range.mp hi)
    _ = ε / 2 := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => jumpBeta c (q.x i)) q.n,
        q.first, q.last]
      simp [jumpBeta]
    _ < ε := by linarith

/-- The three printed values at the jump. -/
@[simp] theorem beta1_zero : beta1 0 = 0 := by simp [beta1, jumpBeta]
@[simp] theorem beta2_zero : beta2 0 = 1 := by simp [beta2, jumpBeta]
@[simp] theorem beta3_zero : beta3 0 = 1 / 2 := by simp [beta3, jumpBeta]

/-- All three source integrators vanish strictly to the left of zero. -/
theorem exercise03_beta_negative {x : ℝ} (hx : x < 0) :
    beta1 x = 0 ∧ beta2 x = 0 ∧ beta3 x = 0 := by
  simp [beta1, beta2, beta3, jumpBeta, hx]

/-- All three source integrators equal one strictly to the right of zero. -/
theorem exercise03_beta_positive {x : ℝ} (hx : 0 < x) :
    beta1 x = 1 ∧ beta2 x = 1 ∧ beta3 x = 1 := by
  simp [beta1, beta2, beta3, jumpBeta, not_lt.mpr hx.le, hx.ne']

/-- R06E03(a), sufficient direction: right continuity at zero constructs the
literal Darboux integral, with its actual value. -/
theorem exercise03_a_integral {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M)
    (hr : ContinuousWithinAt f (Ici 0) 0) :
    HasDarbouxRSIntegral f beta1 (-1) 1 (f 0) := by
  exact hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num)
    (beta_sufficient (by norm_num) (by norm_num) hb (fun _ => hr) (by norm_num))

/-- R06E03(a): bounded functions are integrable exactly when the right limit
at zero is their value at zero. No left continuity is assumed. -/
theorem exercise03_a_integrability {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M) :
    (∃ v : ℝ, HasDarbouxRSIntegral f beta1 (-1) 1 v) ↔
      ContinuousWithinAt f (Ici 0) 0 := by
  constructor
  · rintro ⟨v, hv⟩
    exact beta_right_necessary (by norm_num) (by norm_num)
      (hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hv)
  · exact fun hr => ⟨f 0, exercise03_a_integral hb hr⟩

/-- R06E03(a), value: every literal integral against the first raw step has
value `f 0`. -/
theorem exercise03_a_value {f : ℝ → ℝ} {v : ℝ}
    (hv : HasDarbouxRSIntegral f beta1 (-1) 1 v) : v = f 0 :=
  beta_integral_value (hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hv)

/-- R06E03(b), sufficient direction for the second raw step. -/
theorem exercise03_b_integral {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M)
    (hl : ContinuousWithinAt f (Iic 0) 0) :
    HasDarbouxRSIntegral f beta2 (-1) 1 (f 0) := by
  exact hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num)
    (beta_sufficient (by norm_num) (by norm_num) hb (by norm_num) (fun _ => hl))

/-- R06E03(b): the second raw step requires precisely left continuity at zero. -/
theorem exercise03_b_integrability {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M) :
    (∃ v : ℝ, HasDarbouxRSIntegral f beta2 (-1) 1 v) ↔
      ContinuousWithinAt f (Iic 0) 0 := by
  constructor
  · rintro ⟨v, hv⟩
    exact beta_left_necessary (by norm_num) (by norm_num)
      (hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hv)
  · exact fun hl => ⟨f 0, exercise03_b_integral hb hl⟩

/-- R06E03(b), value, without substituting the right-normalized integrator. -/
theorem exercise03_b_value {f : ℝ → ℝ} {v : ℝ}
    (hv : HasDarbouxRSIntegral f beta2 (-1) 1 v) : v = f 0 :=
  beta_integral_value (hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hv)

/-- R06E03(c), sufficient direction and actual value for the half-valued step. -/
theorem exercise03_c_integral {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M) (hf : ContinuousAt f 0) :
    HasDarbouxRSIntegral f beta3 (-1) 1 (f 0) := by
  exact hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num)
    (beta_sufficient (by norm_num) (by norm_num) hb
      (fun _ => hf.continuousWithinAt) (fun _ => hf.continuousWithinAt))

/-- R06E03(c): the two nonzero half-jumps force full continuity at zero.
The necessary direction extracts both one-sided continuities from the integral. -/
theorem exercise03_c_integrability {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M) :
    (∃ v : ℝ, HasDarbouxRSIntegral f beta3 (-1) 1 v) ↔ ContinuousAt f 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have ht := hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hv
    have hr := beta_right_necessary (by norm_num) (by norm_num) ht
    have hl := beta_left_necessary (by norm_num) (by norm_num) ht
    simpa only [Iic_union_Ici, continuousWithinAt_univ] using hl.union hr
  · exact fun hf => ⟨f 0, exercise03_c_integral hb hf⟩

/-- The third raw integral also has the actual value `f 0`. -/
theorem exercise03_c_value {f : ℝ → ℝ} {v : ℝ}
    (hv : HasDarbouxRSIntegral f beta3 (-1) 1 v) : v = f 0 :=
  beta_integral_value (hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hv)

/-- R06E03(d): continuity only at zero gives all three actual integrals,
each with value `f 0`. -/
theorem exercise03_d {f : ℝ → ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |f x| ≤ M) (hf : ContinuousAt f 0) :
    HasDarbouxRSIntegral f beta1 (-1) 1 (f 0) ∧
    HasDarbouxRSIntegral f beta2 (-1) 1 (f 0) ∧
    HasDarbouxRSIntegral f beta3 (-1) 1 (f 0) :=
  ⟨exercise03_a_integral hb hf.continuousWithinAt,
    exercise03_b_integral hb hf.continuousWithinAt, exercise03_c_integral hb hf⟩

end Rudin.Chapter06
