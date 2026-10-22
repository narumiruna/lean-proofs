module

public import Math.Rudin.Support.StieltjesPrototype
public import Mathlib.Data.Finset.Sort

/-!
Refinement and sum bounds for the weak partitions of `StieltjesPrototype`.
The construction sorts a finite set of vertices and repeats its last vertex.
Thus even a singleton vertex set gives a genuine one-cell partition.
Source: Rudin, Definitions 6.1–6.3 and Theorems 6.4–6.7,
book pages 120–125 (PDF 129–134).
This file proves refinement monotonicity and the Darboux-to-tagged direction.
The tagged-to-Darboux converse and nonconstant measure bridges remain open.
-/

@[expose] public section

namespace Rudin.Support.StieltjesRefinement

open Set StieltjesPrototype

variable {a b : ℝ}

theorem refines_refl (p : Partition a b) : Refines p p := Subset.rfl

theorem refines_trans {p q r : Partition a b}
    (hpq : Refines p q) (hqr : Refines q r) : Refines p r := hqr.trans hpq

/-- Every used node is in the original closed interval. -/
theorem node_mem (p : Partition a b) {i : ℕ} (hi : i ≤ p.n) : p.x i ∈ Icc a b := by
  constructor
  · simpa only [p.first] using p.increasing (by simp) hi (Nat.zero_le i)
  · simpa only [p.last] using p.increasing hi (by simp) hi

theorem endpoints_le (p : Partition a b) : a ≤ b := by
  simpa only [p.first] using (node_mem p (Nat.zero_le p.n)).2

/-- The finite set of used vertices, without multiplicities. -/
noncomputable def vertices (p : Partition a b) : Finset ℝ :=
  (Finset.range (p.n + 1)).image p.x

@[simp] theorem mem_vertices (p : Partition a b) (z : ℝ) :
    z ∈ vertices p ↔ z ∈ p.x '' Iic p.n := by
  classical
  simp only [vertices, Finset.mem_image, Finset.mem_range, mem_image, mem_Iic]
  constructor <;> rintro ⟨i, hi, rfl⟩ <;> exact ⟨i, by omega, rfl⟩

/-- Enumerate distinct vertices in increasing order, then repeat the last vertex. -/
noncomputable def sortedNode (s : Finset ℝ) (hs : 0 < s.card) (i : ℕ) : ℝ :=
  s.orderEmbOfFin rfl ⟨min i (s.card - 1), by omega⟩

theorem sortedNode_mono (s : Finset ℝ) (hs : 0 < s.card) :
    Monotone (sortedNode s hs) := by
  intro i j hij
  exact (s.orderEmbOfFin rfl).monotone (show min i (s.card - 1) ≤ min j (s.card - 1)
    from min_le_min_right _ hij)

/-- Sort a nonempty vertex set in `[a,b]`, with one repeated final node.
The number of cells is the number of distinct vertices, including when `a = b`. -/
noncomputable def ofVertices (s : Finset ℝ) (ha : a ∈ s) (hb : b ∈ s)
    (hs : ∀ z ∈ s, z ∈ Icc a b) : Partition a b where
  n := s.card
  pos := Finset.card_pos.mpr ⟨a, ha⟩
  x := sortedNode s (Finset.card_pos.mpr ⟨a, ha⟩)
  first := by
    have hpos := Finset.card_pos.mpr (show s.Nonempty from ⟨a, ha⟩)
    unfold sortedNode
    simp only [Nat.zero_min]
    rw [Finset.orderEmbOfFin_zero rfl hpos]
    exact (Finset.min'_eq_iff _ _ _).mpr ⟨ha, fun z hz ↦ (hs z hz).1⟩
  last := by
    have hpos := Finset.card_pos.mpr (show s.Nonempty from ⟨a, ha⟩)
    unfold sortedNode
    simp only [min_eq_right (Nat.sub_le _ _)]
    rw [Finset.orderEmbOfFin_last rfl hpos]
    exact (Finset.max'_eq_iff _ _ _).mpr ⟨hb, fun z hz ↦ (hs z hz).2⟩
  increasing := (sortedNode_mono s _).monotoneOn _

/-- Sorting preserves exactly the vertex set, also for singleton sets. -/
theorem ofVertices_nodes (s : Finset ℝ) (ha : a ∈ s) (hb : b ∈ s)
    (hs : ∀ z ∈ s, z ∈ Icc a b) :
    (ofVertices s ha hb hs).x '' Iic (ofVertices s ha hb hs).n = (s : Set ℝ) := by
  ext z
  constructor
  · rintro ⟨i, _, rfl⟩
    exact s.orderEmbOfFin_mem rfl _
  · intro hz
    obtain ⟨j, hj⟩ := (s.orderIsoOfFin rfl).surjective ⟨z, hz⟩
    refine ⟨j.val, Nat.le_of_lt j.isLt, ?_⟩
    change sortedNode s (Finset.card_pos.mpr ⟨a, ha⟩) j.val = z
    unfold sortedNode
    have hmin : min j.val (s.card - 1) = j.val := min_eq_left (by omega)
    simp only [hmin]
    exact congrArg Subtype.val hj

/-- The common refinement has exactly the union of the original vertex sets. -/
noncomputable def commonRefinement (p q : Partition a b) : Partition a b :=
  ofVertices (vertices p ∪ vertices q)
    (Finset.mem_union_left _ ((mem_vertices p a).mpr ⟨0, by simp, p.first⟩))
    (Finset.mem_union_left _ ((mem_vertices p b).mpr ⟨p.n, by simp, p.last⟩))
    (by
      intro z hz
      rcases Finset.mem_union.mp hz with hp | hq
      · obtain ⟨i, hi, rfl⟩ := (mem_vertices p z).mp hp
        exact node_mem p hi
      · obtain ⟨i, hi, rfl⟩ := (mem_vertices q z).mp hq
        exact node_mem q hi)

theorem commonRefinement_nodes (p q : Partition a b) :
    (commonRefinement p q).x '' Iic (commonRefinement p q).n =
      (p.x '' Iic p.n) ∪ (q.x '' Iic q.n) := by
  rw [commonRefinement, ofVertices_nodes]
  ext z
  simp only [Finset.coe_union, mem_union, Finset.mem_coe, mem_vertices]

theorem commonRefinement_refines_left (p q : Partition a b) :
    Refines (commonRefinement p q) p := by
  unfold Refines
  rw [commonRefinement_nodes]
  exact subset_union_left

theorem commonRefinement_refines_right (p q : Partition a b) :
    Refines (commonRefinement p q) q := by
  unfold Refines
  rw [commonRefinement_nodes]
  exact subset_union_right

theorem exists_common_refinement (p q : Partition a b) :
    ∃ r : Partition a b, Refines r p ∧ Refines r q :=
  ⟨commonRefinement p q, commonRefinement_refines_left p q,
    commonRefinement_refines_right p q⟩

/-- Every cell, including a repeated-node cell, is a subset of `[a,b]`. -/
theorem cell_subset (p : Partition a b) {i : ℕ} (hi : i < p.n) :
    Icc (p.x i) (p.x (i + 1)) ⊆ Icc a b := by
  intro z hz
  exact ⟨(node_mem p (by omega)).1.trans hz.1,
    hz.2.trans (node_mem p (by omega)).2⟩

theorem increment_nonneg (p : Partition a b) {α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) {i : ℕ} (hi : i < p.n) :
    0 ≤ α (p.x (i + 1)) - α (p.x i) :=
  sub_nonneg.mpr (hα (node_mem p (by omega)) (node_mem p (by omega))
    (p.increasing (Nat.le_of_lt hi) (Nat.succ_le_of_lt hi) (Nat.le_succ i)))

private theorem cell_image_nonempty (p : Partition a b) (f : ℝ → ℝ)
    {i : ℕ} (hi : i < p.n) : (f '' Icc (p.x i) (p.x (i + 1))).Nonempty :=
  ⟨f (p.x i), mem_image_of_mem f (left_isTag p i hi)⟩

private theorem cell_bddBelow (p : Partition a b) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n) :
    BddBelow (f '' Icc (p.x i) (p.x (i + 1))) := by
  refine ⟨-M, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (abs_le.mp (hf z (cell_subset p hi hz))).1

private theorem cell_bddAbove (p : Partition a b) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n) :
    BddAbove (f '' Icc (p.x i) (p.x (i + 1))) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (abs_le.mp (hf z (cell_subset p hi hz))).2

/-- The lower sum bounds every admissible tagged sum, without strict nodes. -/
theorem lowerSum_le_taggedSum (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    {tag : ℕ → ℝ} (htag : IsTag p tag) : lowerSum p f α ≤ taggedSum p f α tag := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_right
    (csInf_le (cell_bddBelow p hf hi') (mem_image_of_mem f (htag i hi')))
    (increment_nonneg p hα hi')

/-- Every admissible tagged sum is bounded by the upper sum. -/
theorem taggedSum_le_upperSum (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    {tag : ℕ → ℝ} (htag : IsTag p tag) : taggedSum p f α tag ≤ upperSum p f α := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_right
    (le_csSup (cell_bddAbove p hf hi') (mem_image_of_mem f (htag i hi')))
    (increment_nonneg p hα hi')

theorem lowerSum_le_upperSum (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    lowerSum p f α ≤ upperSum p f α :=
  (lowerSum_le_taggedSum p hα hf (left_isTag p)).trans
    (taggedSum_le_upperSum p hα hf (left_isTag p))

/-- A uniform lower bound for all lower sums. -/
theorem lowerSum_global_bound (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    -M * (α b - α a) ≤ lowerSum p f α := by
  rw [← lowerSum_const p α (-M)]
  unfold lowerSum
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show (fun _ : ℝ ↦ -M) '' Icc (p.x i) (p.x (i + 1)) = {-M} from
    (nonempty_Icc.mpr (left_isTag p i hi').2).image_const _, csInf_singleton]
  apply mul_le_mul_of_nonneg_right _ (increment_nonneg p hα hi')
  apply le_csInf (cell_image_nonempty p f hi')
  rintro _ ⟨z, hz, rfl⟩
  exact (abs_le.mp (hf z (cell_subset p hi' hz))).1

/-- A uniform upper bound for all upper sums. -/
theorem upperSum_global_bound (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    upperSum p f α ≤ M * (α b - α a) := by
  rw [← upperSum_const p α M]
  unfold upperSum
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show (fun _ : ℝ ↦ M) '' Icc (p.x i) (p.x (i + 1)) = {M} from
    (nonempty_Icc.mpr (left_isTag p i hi').2).image_const _, csSup_singleton]
  apply mul_le_mul_of_nonneg_right _ (increment_nonneg p hα hi')
  apply csSup_le (cell_image_nonempty p f hi')
  rintro _ ⟨z, hz, rfl⟩
  exact (abs_le.mp (hf z (cell_subset p hi' hz))).2

/-- All actual tagged sums satisfy the expected absolute bound. -/
theorem abs_taggedSum_le (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    {tag : ℕ → ℝ} (htag : IsTag p tag) :
    |taggedSum p f α tag| ≤ M * (α b - α a) := by
  apply abs_le.mpr
  constructor
  · simpa only [neg_mul] using (lowerSum_global_bound p hα hf).trans
      (lowerSum_le_taggedSum p hα hf htag)
  · exact (taggedSum_le_upperSum p hα hf htag).trans (upperSum_global_bound p hα hf)

/-- Match coarse vertices to fine indices. The initial index is zero;
other vertices use the last fine index at or below the coarse vertex. -/
noncomputable def refinementIndex (fine coarse : Partition a b) (i : ℕ) : ℕ := by
  classical
  exact if i = 0 then 0 else Nat.findGreatest (fun j ↦ fine.x j ≤ coarse.x i) fine.n

@[simp] theorem refinementIndex_zero (fine coarse : Partition a b) :
    refinementIndex fine coarse 0 = 0 := by
  classical
  simp [refinementIndex]

theorem refinementIndex_le (fine coarse : Partition a b) (i : ℕ) :
    refinementIndex fine coarse i ≤ fine.n := by
  classical
  unfold refinementIndex
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.findGreatest_le _

theorem refinementIndex_mono (fine coarse : Partition a b) :
    MonotoneOn (refinementIndex fine coarse) (Iic coarse.n) := by
  classical
  intro i hi j hj hij
  by_cases hi0 : i = 0
  · subst i
    simp
  · have hj0 : j ≠ 0 := by omega
    simp only [refinementIndex, ite_eq_right hi0, ite_eq_right hj0]
    exact Nat.findGreatest_mono_left
      (fun k hk ↦ hk.trans (coarse.increasing hi hj hij)) _

/-- Refinement matches all coarse vertices, even repeated ones. -/
theorem refinementIndex_node {fine coarse : Partition a b} (h : Refines fine coarse)
    {i : ℕ} (hi : i ≤ coarse.n) :
    fine.x (refinementIndex fine coarse i) = coarse.x i := by
  classical
  by_cases hi0 : i = 0
  · subst i
    simp only [refinementIndex_zero, fine.first, coarse.first]
  · obtain ⟨j, hj, hjx⟩ := h (mem_image_of_mem coarse.x hi)
    simp only [refinementIndex, ite_eq_right hi0]
    apply le_antisymm
    · exact Nat.findGreatest_spec (P := fun j ↦ fine.x j ≤ coarse.x i) hj hjx.le
    · calc
        coarse.x i = fine.x j := hjx.symm
        _ ≤ fine.x (Nat.findGreatest (fun j ↦ fine.x j ≤ coarse.x i) fine.n) :=
          fine.increasing hj (Nat.findGreatest_le _)
            (Nat.le_findGreatest (P := fun j ↦ fine.x j ≤ coarse.x i) hj hjx.le)

@[simp] theorem refinementIndex_last (fine coarse : Partition a b) :
    refinementIndex fine coarse coarse.n = fine.n := by
  classical
  simp only [refinementIndex, ite_eq_right (Nat.ne_of_gt coarse.pos)]
  exact Nat.findGreatest_eq (by rw [fine.last, coarse.last])

private theorem sum_blocks (fine coarse : Partition a b) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range coarse.n,
      ∑ j ∈ Finset.Ico (refinementIndex fine coarse i) (refinementIndex fine coarse (i + 1)),
        g j) = ∑ j ∈ Finset.range fine.n, g j := by
  have hblock : ∀ i ∈ Finset.range coarse.n,
      (∑ j ∈ Finset.Ico (refinementIndex fine coarse i) (refinementIndex fine coarse (i + 1)),
        g j) = (∑ j ∈ Finset.range (refinementIndex fine coarse (i + 1)), g j) -
          ∑ j ∈ Finset.range (refinementIndex fine coarse i), g j := by
    intro i hi
    apply Finset.sum_Ico_eq_sub
    exact refinementIndex_mono fine coarse (by exact Nat.le_of_lt (Finset.mem_range.mp hi))
      (by exact Nat.succ_le_of_lt (Finset.mem_range.mp hi)) (Nat.le_succ i)
  simp_rw [Finset.sum_congr rfl hblock]
  rw [Finset.sum_range_sub (fun i ↦ ∑ j ∈ Finset.range (refinementIndex fine coarse i), g j),
    refinementIndex_last, refinementIndex_zero]
  simp

private theorem increment_sum (p : Partition a b) (α : ℝ → ℝ) {j k : ℕ} (hjk : j ≤ k) :
    (∑ t ∈ Finset.Ico j k, (α (p.x (t + 1)) - α (p.x t))) =
      α (p.x k) - α (p.x j) := by
  rw [Finset.sum_Ico_eq_sub _ hjk,
    Finset.sum_range_sub (fun t ↦ α (p.x t)), Finset.sum_range_sub (fun t ↦ α (p.x t))]
  ring

/-- Each fine cell in a matched index block lies in its coarse cell. -/
theorem refinement_cell_subset {fine coarse : Partition a b} (h : Refines fine coarse)
    {i j : ℕ} (hi : i < coarse.n)
    (hj : j ∈ Finset.Ico (refinementIndex fine coarse i) (refinementIndex fine coarse (i + 1))) :
    Icc (fine.x j) (fine.x (j + 1)) ⊆ Icc (coarse.x i) (coarse.x (i + 1)) := by
  have hj' := Finset.mem_Ico.mp hj
  have hji : j ≤ fine.n := by have := refinementIndex_le fine coarse (i + 1); omega
  have hjs : j + 1 ≤ fine.n := by have := refinementIndex_le fine coarse (i + 1); omega
  intro z hz
  constructor
  · rw [← refinementIndex_node h (Nat.le_of_lt hi)]
    exact (fine.increasing (refinementIndex_le fine coarse i) hji hj'.1).trans hz.1
  · rw [← refinementIndex_node h (Nat.succ_le_of_lt hi)]
    exact hz.2.trans (fine.increasing hjs (refinementIndex_le fine coarse (i + 1))
      (Nat.succ_le_of_lt hj'.2))

/-- Lower sums increase under the existing vertex-subset refinement relation. -/
theorem lowerSum_mono_refinement {fine coarse : Partition a b} (h : Refines fine coarse)
    {f α : ℝ → ℝ} {M : ℝ} (hα : MonotoneOn α (Icc a b))
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) : lowerSum coarse f α ≤ lowerSum fine f α := by
  unfold lowerSum
  rw [← sum_blocks fine coarse]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hei := refinementIndex_mono fine coarse (Nat.le_of_lt hi')
    (Nat.succ_le_of_lt hi') (Nat.le_succ i)
  rw [← refinementIndex_node h (Nat.le_of_lt hi'),
    ← refinementIndex_node h (Nat.succ_le_of_lt hi'), ← increment_sum fine α hei,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hjn : j < fine.n := lt_of_lt_of_le hj'.2 (refinementIndex_le fine coarse (i + 1))
  apply mul_le_mul_of_nonneg_right _ (increment_nonneg fine hα hjn)
  rw [refinementIndex_node h (Nat.le_of_lt hi'),
    refinementIndex_node h (Nat.succ_le_of_lt hi')]
  apply le_csInf (cell_image_nonempty fine f hjn)
  rintro _ ⟨z, hz, rfl⟩
  exact csInf_le (cell_bddBelow coarse hf hi')
    (mem_image_of_mem f (refinement_cell_subset h hi' hj hz))

/-- Upper sums decrease under refinement; zero increments require no division. -/
theorem upperSum_anti_refinement {fine coarse : Partition a b} (h : Refines fine coarse)
    {f α : ℝ → ℝ} {M : ℝ} (hα : MonotoneOn α (Icc a b))
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) : upperSum fine f α ≤ upperSum coarse f α := by
  unfold upperSum
  rw [← sum_blocks fine coarse]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hei := refinementIndex_mono fine coarse (Nat.le_of_lt hi')
    (Nat.succ_le_of_lt hi') (Nat.le_succ i)
  rw [← refinementIndex_node h (Nat.le_of_lt hi'),
    ← refinementIndex_node h (Nat.succ_le_of_lt hi'), ← increment_sum fine α hei,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hjn : j < fine.n := lt_of_lt_of_le hj'.2 (refinementIndex_le fine coarse (i + 1))
  apply mul_le_mul_of_nonneg_right _ (increment_nonneg fine hα hjn)
  rw [refinementIndex_node h (Nat.le_of_lt hi'),
    refinementIndex_node h (Nat.succ_le_of_lt hi')]
  apply csSup_le (cell_image_nonempty fine f hjn)
  rintro _ ⟨z, hz, rfl⟩
  exact le_csSup (cell_bddAbove coarse hf hi')
    (mem_image_of_mem f (refinement_cell_subset h hi' hj hz))

/-- Every lower sum is below every upper sum, not only for a fixed partition. -/
theorem lowerSum_le_upperSum_of_partitions (p q : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    lowerSum p f α ≤ upperSum q f α :=
  (lowerSum_mono_refinement (commonRefinement_refines_left p q) hα hf).trans
    ((lowerSum_le_upperSum (commonRefinement p q) hα hf).trans
      (upperSum_anti_refinement (commonRefinement_refines_right p q) hα hf))

/-- The lower-sum range has genuine finite bounds. -/
theorem lowerSum_range_bounded {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    BddBelow (Set.range fun p : Partition a b ↦ lowerSum p f α) ∧
      BddAbove (Set.range fun p : Partition a b ↦ lowerSum p f α) := by
  constructor
  · refine ⟨-M * (α b - α a), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact lowerSum_global_bound p hα hf
  · refine ⟨M * (α b - α a), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (lowerSum_le_upperSum p hα hf).trans (upperSum_global_bound p hα hf)

/-- The upper-sum range also has genuine finite bounds. -/
theorem upperSum_range_bounded {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    BddBelow (Set.range fun p : Partition a b ↦ upperSum p f α) ∧
      BddAbove (Set.range fun p : Partition a b ↦ upperSum p f α) := by
  constructor
  · refine ⟨-M * (α b - α a), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (lowerSum_global_bound p hα hf).trans (lowerSum_le_upperSum p hα hf)
  · refine ⟨M * (α b - α a), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact upperSum_global_bound p hα hf

/-- The lower Darboux integral does not exceed the upper one.
`hab` supplies a partition even when `a = b`; no empty extrema are used. -/
theorem lowerIntegral_le_upperIntegral (hab : a ≤ b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    sSup (Set.range fun p : Partition a b ↦ lowerSum p f α) ≤
      sInf (Set.range fun p : Partition a b ↦ upperSum p f α) := by
  apply csSup_le (s := Set.range fun p : Partition a b ↦ lowerSum p f α)
    ⟨lowerSum (single hab) f α, ⟨single hab, rfl⟩⟩
  rintro _ ⟨p, rfl⟩
  apply le_csInf (s := Set.range fun p : Partition a b ↦ upperSum p f α)
    ⟨upperSum (single hab) f α, ⟨single hab, rfl⟩⟩
  rintro _ ⟨q, rfl⟩
  exact lowerSum_le_upperSum_of_partitions p q hα hf

/-- Darboux integrability gives the actual refinement-based tagged criterion. -/
theorem hasRSIntegral_of_hasDarbouxRSIntegral (hab : a ≤ b) {f α : ℝ → ℝ} {value : ℝ}
    (h : HasDarbouxRSIntegral f α a b value) : HasRSIntegral f α a b value := by
  obtain ⟨hα, ⟨M, hf⟩, hl, hu⟩ := h
  refine ⟨hα, ⟨M, hf⟩, ?_⟩
  intro ε hε
  have hlne : (Set.range fun p : Partition a b ↦ lowerSum p f α).Nonempty :=
    ⟨_, ⟨single hab, rfl⟩⟩
  have hune : (Set.range fun p : Partition a b ↦ upperSum p f α).Nonempty :=
    ⟨_, ⟨single hab, rfl⟩⟩
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_lt_csSup hlne
    (show value - ε < sSup (Set.range fun p : Partition a b ↦ lowerSum p f α) by
      rw [hl]; linarith)
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := exists_lt_of_csInf_lt hune
    (show sInf (Set.range fun p : Partition a b ↦ upperSum p f α) < value + ε by
      rw [hu]; linarith)
  refine ⟨commonRefinement p q, ?_⟩
  intro r hr tag htag
  have hrp := refines_trans hr (commonRefinement_refines_left p q)
  have hrq := refines_trans hr (commonRefinement_refines_right p q)
  have hlow := (lowerSum_mono_refinement hrp hα hf).trans
    (lowerSum_le_taggedSum r hα hf htag)
  have hupp := (taggedSum_le_upperSum r hα hf htag).trans
    (upperSum_anti_refinement hrq hα hf)
  apply abs_lt.mpr
  constructor <;> linarith

/-- The tagged criterion has a unique value, by an actual common refinement. -/
theorem hasRSIntegral_unique {f α : ℝ → ℝ} {v w : ℝ}
    (hv : HasRSIntegral f α a b v) (hw : HasRSIntegral f α a b w) : v = w := by
  by_contra hne
  have hdist : 0 < |v - w| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨p, hp⟩ := hv.2.2 (|v - w| / 2) (by positivity)
  obtain ⟨q, hq⟩ := hw.2.2 (|v - w| / 2) (by positivity)
  let r := commonRefinement p q
  have hv' := hp r (commonRefinement_refines_left p q) r.x (left_isTag r)
  have hw' := hq r (commonRefinement_refines_right p q) r.x (left_isTag r)
  have htriangle : |v - w| ≤ |taggedSum r f α r.x - v| + |taggedSum r f α r.x - w| := by
    calc
      |v - w| = |-(taggedSum r f α r.x - v) + (taggedSum r f α r.x - w)| := by congr 1; ring
      _ ≤ |-(taggedSum r f α r.x - v)| + |taggedSum r f α r.x - w| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  linarith

/-- A singleton interval has exactly one distinct vertex in every partition. -/
@[simp] theorem vertices_self (p : Partition a a) : vertices p = {a} := by
  classical
  ext z
  rw [mem_vertices, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact node_eq_of_self p hi
  · rintro rfl
    exact ⟨0, by simp, p.first⟩

/-- The common refinement on `[a,a]` is genuinely a one-cell partition. -/
@[simp] theorem commonRefinement_self_n (p q : Partition a a) :
    (commonRefinement p q).n = 1 := by
  classical
  change (vertices p ∪ vertices q).card = 1
  simp

/-- On a singleton interval the tagged criterion also gives zero for arbitrary functions. -/
theorem hasRSIntegral_self (f α : ℝ → ℝ) (a : ℝ) : HasRSIntegral f α a a 0 :=
  hasRSIntegral_of_hasDarbouxRSIntegral le_rfl (hasDarbouxRSIntegral_self f α a)

/-- Every singleton partition has the same vertex set as the genuine one-cell partition. -/
theorem refines_degenerate (p : Partition a a) :
    Refines p (degenerate a) ∧ Refines (degenerate a) p := by
  constructor
  · rintro _ ⟨i, _, rfl⟩
    rw [degenerate_x]
    exact ⟨0, by simp, p.first⟩
  · rintro _ ⟨i, hi, rfl⟩
    rw [node_eq_of_self p hi]
    exact ⟨0, by simp, by simp⟩

end Rudin.Support.StieltjesRefinement
