module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
A restricted Riemann–Stieltjes prototype on `a ≤ b`.
Partitions have weakly increasing nodes, as in Rudin's Definition 6.1
(book page 120, PDF page 129). Repeated nodes include zero-length intervals.
The tagged sums use the actual integrator values, not right limits.
The convergence predicate controls every tagged refinement of one partition.
Only constant integrands are bridged to a measure integral here.
-/

@[expose] public section

namespace Rudin.Support.StieltjesPrototype

open Set MeasureTheory

/-- A finite, weakly increasing partition. Values after `n` are not used.
There is at least one cell, including when the interval is a singleton. -/
structure Partition (a b : ℝ) where
  n : ℕ
  pos : 0 < n
  x : ℕ → ℝ
  first : x 0 = a
  last : x n = b
  increasing : MonotoneOn x (Iic n)

/-- The partition with one subinterval. -/
def single {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  pos := by decide
  x := fun i ↦ if i = 0 then a else b
  first := by simp
  last := by simp
  increasing := by
    intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all

/-- A real one-cell partition of `[a,a]`, with both nodes equal to `a`. -/
def degenerate (a : ℝ) : Partition a a := single le_rfl

@[simp] theorem degenerate_n (a : ℝ) : (degenerate a).n = 1 := rfl

@[simp] theorem degenerate_x (a : ℝ) (i : ℕ) : (degenerate a).x i = a := by
  simp [degenerate, single]

/-- Every used node of every partition of `[a,a]` equals `a`. -/
theorem node_eq_of_self {a : ℝ} (p : Partition a a) {i : ℕ} (hi : i ≤ p.n) :
    p.x i = a := by
  apply le_antisymm
  · simpa only [p.last] using p.increasing hi (by simp) hi
  · simpa only [p.first] using p.increasing (by simp) hi (Nat.zero_le i)

/-- All nodes of the coarse partition occur in the finer partition. -/
def Refines {a b : ℝ} (fine coarse : Partition a b) : Prop :=
  coarse.x '' Iic coarse.n ⊆ fine.x '' Iic fine.n

/-- Tags may be either endpoint of each closed subinterval. -/
def IsTag {a b : ℝ} (p : Partition a b) (tag : ℕ → ℝ) : Prop :=
  ∀ i < p.n, tag i ∈ Icc (p.x i) (p.x (i + 1))

/-- Every partition has admissible tags, including its left endpoints. -/
theorem left_isTag {a b : ℝ} (p : Partition a b) : IsTag p p.x := by
  intro i hi
  refine ⟨le_rfl, p.increasing ?_ ?_ (Nat.le_succ i)⟩
  · exact Nat.le_of_lt hi
  · exact Nat.succ_le_of_lt hi

/-- A sum with Rudin's increments `α(xᵢ₊₁) - α(xᵢ)`. -/
noncomputable def taggedSum {a b : ℝ} (p : Partition a b)
    (f α : ℝ → ℝ) (tag : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n, f (tag i) * (α (p.x (i + 1)) - α (p.x i))

/-- Refinement-based tagged-sum criterion; no identification with Darboux integrals is assumed. -/
def HasRSIntegral (f α : ℝ → ℝ) (a b value : ℝ) : Prop :=
  MonotoneOn α (Icc a b) ∧ (∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) ∧
    ∀ ε > (0 : ℝ), ∃ p : Partition a b,
    ∀ q : Partition a b, Refines q p → ∀ tag : ℕ → ℝ, IsTag q tag →
      |taggedSum q f α tag - value| < ε

/-- Every tagged sum of a constant telescopes, including at jumps and endpoints. -/
theorem taggedSum_const {a b : ℝ} (p : Partition a b) (α : ℝ → ℝ)
    (c : ℝ) (tag : ℕ → ℝ) :
    taggedSum p (fun _ ↦ c) α tag = c * (α b - α a) := by
  rw [taggedSum, ← Finset.mul_sum,
    Finset.sum_range_sub (fun i ↦ α (p.x i)) p.n, p.first, p.last]

/-- Constants satisfy the tagged refinement criterion for every monotone integrator. -/
theorem hasRSIntegral_const {a b : ℝ} (hab : a < b) {α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (c : ℝ) :
    HasRSIntegral (fun _ ↦ c) α a b (c * (α b - α a)) := by
  refine ⟨hα, ⟨|c|, fun _ _ ↦ le_rfl⟩, fun ε hε ↦ ⟨single hab.le, fun q _ tag _ ↦ ?_⟩⟩
  simpa [taggedSum_const] using hε

/-- The constant case is not vacuous: no other value satisfies the criterion. -/
theorem constant_value_unique {a b c value : ℝ} {α : ℝ → ℝ}
    (h : HasRSIntegral (fun _ ↦ c) α a b value) : value = c * (α b - α a) := by
  by_contra hne
  have hpos : 0 < |c * (α b - α a) - value| :=
    abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨p, hp⟩ := h.2.2 _ hpos
  have herror := hp p (show Refines p p from Subset.rfl) p.x (left_isTag p)
  rw [taggedSum_const] at herror
  exact (lt_irrefl _ herror)

/-- The measure integral agrees with these genuine tagged sums for constants.
Right continuity is supplied by `StieltjesFunction`; `(a,b]` excludes a jump at `a`.
This theorem does not give a bridge for nonconstant integrands. -/
theorem constant_bridge (α : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) (c : ℝ) :
    HasRSIntegral (fun _ ↦ c) α a b (∫ _ in a..b, c ∂α.measure) := by
  have hvalue : (∫ _ in a..b, c ∂α.measure) = c * (α b - α a) := by
    rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.setIntegral_const,
      Measure.real, α.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (α.mono hab.le))]
    simp [smul_eq_mul, mul_comm]
  rw [hvalue]
  exact hasRSIntegral_const hab (α.mono.monotoneOn _) c

-- The interval and atom formulas fix the endpoint convention explicitly.
theorem interval_mass (α : StieltjesFunction ℝ) (a b : ℝ) :
    α.measure (Ioc a b) = ENNReal.ofReal (α b - α a) := α.measure_Ioc a b

theorem jump_mass (α : StieltjesFunction ℝ) (a : ℝ) :
    α.measure {a} = ENNReal.ofReal (α a - Function.leftLim α a) := α.measure_singleton a

/-- Rudin's lower Darboux sum, with infima on closed subintervals. -/
noncomputable def lowerSum {a b : ℝ} (p : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n,
    sInf (f '' Icc (p.x i) (p.x (i + 1))) * (α (p.x (i + 1)) - α (p.x i))

/-- Rudin's upper Darboux sum, with suprema on closed subintervals. -/
noncomputable def upperSum {a b : ℝ} (p : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n,
    sSup (f '' Icc (p.x i) (p.x (i + 1))) * (α (p.x (i + 1)) - α (p.x i))

/-- The literal lower/upper integral criterion, separate from the tagged criterion.
Boundedness is required because real conditional suprema are otherwise unspecified. -/
def HasDarbouxRSIntegral (f α : ℝ → ℝ) (a b value : ℝ) : Prop :=
  MonotoneOn α (Icc a b) ∧ (∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) ∧
  sSup (Set.range fun p : Partition a b ↦ lowerSum p f α) = value ∧
  sInf (Set.range fun p : Partition a b ↦ upperSum p f α) = value

private theorem constant_image {a b : ℝ} (p : Partition a b) (c : ℝ) {i : ℕ} (hi : i < p.n) :
    (fun _ : ℝ ↦ c) '' Icc (p.x i) (p.x (i + 1)) = {c} := by
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    rfl
  · intro hy
    have hyc : y = c := hy
    subst y
    exact ⟨p.x i, left_isTag p i hi, rfl⟩

theorem lowerSum_const {a b : ℝ} (p : Partition a b) (α : ℝ → ℝ) (c : ℝ) :
    lowerSum p (fun _ ↦ c) α = c * (α b - α a) := by
  rw [← taggedSum_const p α c p.x]
  unfold lowerSum taggedSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [constant_image p c (Finset.mem_range.mp hi), csInf_singleton]

theorem upperSum_const {a b : ℝ} (p : Partition a b) (α : ℝ → ℝ) (c : ℝ) :
    upperSum p (fun _ ↦ c) α = c * (α b - α a) := by
  rw [← taggedSum_const p α c p.x]
  unfold upperSum taggedSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [constant_image p c (Finset.mem_range.mp hi), csSup_singleton]

/-- Constants satisfy Rudin's actual Darboux definition, without continuity of `α`. -/
theorem hasDarbouxRSIntegral_const {a b : ℝ} (hab : a < b) {α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (c : ℝ) :
    HasDarbouxRSIntegral (fun _ ↦ c) α a b (c * (α b - α a)) := by
  let : Nonempty (Partition a b) := ⟨single hab.le⟩
  refine ⟨hα, ⟨|c|, fun _ _ ↦ le_rfl⟩, ?_, ?_⟩ <;>
    simp only [lowerSum_const, upperSum_const, Set.range_const, csSup_singleton, csInf_singleton]

/-- Every lower sum on `[a,a]` is zero, because every increment is zero. -/
theorem lowerSum_self {a : ℝ} (p : Partition a a) (f α : ℝ → ℝ) :
    lowerSum p f α = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [node_eq_of_self p (show i + 1 ≤ p.n by omega),
    node_eq_of_self p (show i ≤ p.n by omega), sub_self, mul_zero]

/-- Every upper sum on `[a,a]` is zero, because every increment is zero. -/
theorem upperSum_self {a : ℝ} (p : Partition a a) (f α : ℝ → ℝ) :
    upperSum p f α = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [node_eq_of_self p (show i + 1 ≤ p.n by omega),
    node_eq_of_self p (show i ≤ p.n by omega), sub_self, mul_zero]

/-- Any real functions have Darboux integral zero on `[a,a]`.
The partition family contains `degenerate a`; neither extremum is over an empty set. -/
theorem hasDarbouxRSIntegral_self (f α : ℝ → ℝ) (a : ℝ) :
    HasDarbouxRSIntegral f α a a 0 := by
  let : Nonempty (Partition a a) := ⟨degenerate a⟩
  refine ⟨?_, ⟨|f a|, ?_⟩, ?_, ?_⟩
  · intro x hx y hy _
    have hx' : x = a := le_antisymm hx.2 hx.1
    have hy' : y = a := le_antisymm hy.2 hy.1
    simp [hx', hy']
  · intro x hx
    have hx' : x = a := le_antisymm hx.2 hx.1
    simp [hx']
  · simp only [lowerSum_self, Set.range_const, csSup_singleton]
  · simp only [upperSum_self, Set.range_const, csInf_singleton]

/-- A restricted bridge from the actual Darboux integral to the measure integral. -/
theorem darboux_constant_bridge (α : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) (c : ℝ) :
    HasDarbouxRSIntegral (fun _ ↦ c) α a b (∫ _ in a..b, c ∂α.measure) := by
  rw [constant_value_unique (constant_bridge α hab c)]
  exact hasDarbouxRSIntegral_const hab (α.mono.monotoneOn _) c

/-- A monotone jump function whose value at the jump is its left limit. -/
noncomputable def delayedStep (x : ℝ) : ℝ := if 0 < x then 1 else 0

theorem monotone_delayedStep : Monotone delayedStep := by
  intro x y hxy
  by_cases hx : 0 < x
  · simp [delayedStep, hx, hx.trans_le hxy]
  · simp only [delayedStep, ite_eq_right hx]
    split_ifs <;> norm_num

open Filter in
theorem rightLim_delayedStep_zero : Function.rightLim delayedStep 0 = 1 := by
  apply rightLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [delayedStep, show 0 < x from hx]

open Filter in
theorem rightLim_delayedStep_negOne : Function.rightLim delayedStep (-1) = 0 := by
  apply rightLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 0)] with x hx
  simp [delayedStep, not_lt.mpr hx.2.le]

/-- Right normalization can change even the constant integral at a finite endpoint.
The original sums on `[-1,0]` are zero; the normalized measure integral is one. -/
theorem normalization_changes_endpoint :
    HasDarbouxRSIntegral (fun _ ↦ 1) delayedStep (-1) 0 0 ∧
    (∫ _ in (-1 : ℝ)..0, (1 : ℝ) ∂monotone_delayedStep.stieltjesFunction.measure) = 1 := by
  constructor
  · have hvalue : (1 : ℝ) * (delayedStep 0 - delayedStep (-1)) = 0 := by
      norm_num [delayedStep]
    simpa only [hvalue] using
      hasDarbouxRSIntegral_const (by norm_num : (-1 : ℝ) < 0)
        (monotone_delayedStep.monotoneOn _) 1
  · rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      MeasureTheory.setIntegral_const, Measure.real, StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq,
      rightLim_delayedStep_zero, rightLim_delayedStep_negOne]
    norm_num

#print axioms hasRSIntegral_const
#print axioms constant_value_unique
#print axioms constant_bridge
#print axioms normalization_changes_endpoint
#print axioms hasDarbouxRSIntegral_const
#print axioms darboux_constant_bridge

end Rudin.Support.StieltjesPrototype
