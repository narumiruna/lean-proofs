module

public import Mathlib
public import Math.Rudin.Chapter07.Exercise17
public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.UniformIntegralLimits

/-! # Chapter 7, Exercise 25: Euler polygons

Source: PDF pages 179–180, book pages 170–171.
The polygon construction is vector-valued so that Exercise 26 uses the same construction.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Rudin.Chapter07.Euler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The uniform mesh, for a positive number `N` of cells. -/
def mesh (N i : ℕ) : ℝ := (i : ℝ) / N

/-- Euler's recursive nodal values. Explicit `Nat.rec` retains a safe kernel definition. -/
def node (φ : ℝ → E → E) (c : E) (N : ℕ) : ℕ → E :=
  Nat.rec c (fun i z => z + (N : ℝ)⁻¹ • φ (mesh N i) z)

@[simp] theorem node_zero (φ : ℝ → E → E) (c : E) (N : ℕ) : node φ c N 0 = c := rfl

@[simp] theorem node_succ (φ : ℝ → E → E) (c : E) (N i : ℕ) :
    node φ c N (i + 1) = node φ c N i + (N : ℝ)⁻¹ • φ (mesh N i) (node φ c N i) := rfl

def slope (φ : ℝ → E → E) (c : E) (N i : ℕ) : E := φ (mesh N i) (node φ c N i)

/-- A clipped affine ramp. -/
def ramp (N i : ℕ) (t : ℝ) : ℝ := min t (mesh N (i + 1)) - min t (mesh N i)

/-- The actual Euler polygon, extended constantly outside the mesh interval. -/
def polygon (φ : ℝ → E → E) (c : E) (N : ℕ) (t : ℝ) : E :=
  c + ∑ i ∈ Finset.range N, ramp N i t • slope φ c N i

lemma mesh_mono {N : ℕ} : Monotone (mesh N) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg N)

lemma mesh_strictMono {N : ℕ} (hN : 0 < N) : StrictMono (mesh N) := by
  intro i j hij
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by exact_mod_cast hN)

@[simp] lemma mesh_zero (N : ℕ) : mesh N 0 = 0 := by simp [mesh]

@[simp] lemma mesh_last {N : ℕ} (hN : 0 < N) : mesh N N = 1 := by
  simp [mesh, ne_of_gt hN]

lemma mesh_step (N i : ℕ) : mesh N (i + 1) - mesh N i = (N : ℝ)⁻¹ := by
  simp only [mesh, Nat.cast_add, Nat.cast_one]
  ring

lemma mesh_mem {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) : mesh N i ∈ Icc (0 : ℝ) 1 :=
  ⟨by unfold mesh; positivity, by simpa [mesh_last hN] using (mesh_mono hi : mesh N i ≤ mesh N N)⟩

lemma ramp_nonneg (N i : ℕ) (t : ℝ) : 0 ≤ ramp N i t := by
  exact sub_nonneg.mpr (min_le_min_left t (mesh_mono (Nat.le_succ i)))

lemma ramp_le (N i : ℕ) (t : ℝ) : ramp N i t ≤ (N : ℝ)⁻¹ := by
  rw [← mesh_step N i]
  unfold ramp
  have hm : mesh N i ≤ mesh N (i + 1) := mesh_mono (Nat.le_succ i)
  by_cases h : t ≤ mesh N i
  · simp only [min_eq_left h, min_eq_left (h.trans hm)]
    linarith
  · have h' := le_of_not_ge h
    rw [min_eq_right h']
    linarith [min_le_right t (mesh N (i + 1))]

lemma ramp_before {N i : ℕ} {t : ℝ} (ht : t ≤ mesh N i) : ramp N i t = 0 := by
  simp [ramp, min_eq_left ht, min_eq_left (ht.trans (mesh_mono (Nat.le_succ i)))]

lemma ramp_after {N i : ℕ} {t : ℝ} (ht : mesh N (i + 1) ≤ t) :
    ramp N i t = (N : ℝ)⁻¹ := by
  rw [ramp, min_eq_right ht, min_eq_right ((mesh_mono (Nat.le_succ i)).trans ht), mesh_step]

lemma ramp_cell {N i : ℕ} {t : ℝ} (ht : t ∈ Icc (mesh N i) (mesh N (i + 1))) :
    ramp N i t = t - mesh N i := by
  simp only [ramp, min_eq_left ht.2, min_eq_right ht.1]

lemma ramp_monotone (N i : ℕ) : Monotone (ramp N i) := by
  intro s t hst
  have hm : mesh N i ≤ mesh N (i + 1) := mesh_mono (Nat.le_succ i)
  by_cases hs : s ≤ mesh N i
  · rw [ramp_before hs]
    exact ramp_nonneg N i t
  · by_cases ht : mesh N (i + 1) ≤ t
    · rw [ramp_after ht]
      exact ramp_le N i s
    · have hsi : mesh N i ≤ s := (lt_of_not_ge hs).le
      have hti : t ≤ mesh N (i + 1) := (lt_of_not_ge ht).le
      rw [ramp_cell ⟨hsi, hst.trans hti⟩, ramp_cell ⟨hsi.trans hst, hti⟩]
      linarith

lemma sum_ramp (N : ℕ) (t : ℝ) :
    ∑ i ∈ Finset.range N, ramp N i t = min t (mesh N N) - min t 0 := by
  unfold ramp
  rw [Finset.sum_range_sub (fun i => min t (mesh N i)), mesh_zero]

lemma sum_ramp_on {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∑ i ∈ Finset.range N, ramp N i t = t := by
  rw [sum_ramp, mesh_last hN, min_eq_left ht.2, min_eq_right ht.1, sub_zero]

lemma polygon_continuous (φ : ℝ → E → E) (c : E) (N : ℕ) : Continuous (polygon φ c N) := by
  unfold polygon ramp
  fun_prop

@[simp] lemma polygon_zero (φ : ℝ → E → E) (c : E) (N : ℕ) : polygon φ c N 0 = c := by
  unfold polygon
  have h (i : ℕ) : ramp N i 0 = 0 := ramp_before (by unfold mesh; positivity)
  simp [h]

lemma node_sum (φ : ℝ → E → E) (c : E) (N i : ℕ) :
    node φ c N i = c + ∑ j ∈ Finset.range i, (N : ℝ)⁻¹ • slope φ c N j := by
  induction i with
  | zero => simp
  | succ i ih => simp only [node_succ, ih, Finset.sum_range_succ, slope]; abel

/-- The polygon has the prescribed affine formula on every closed mesh cell. -/
lemma polygon_cell (φ : ℝ → E → E) (c : E) {N i : ℕ} (hi : i < N)
    {t : ℝ} (ht : t ∈ Icc (mesh N i) (mesh N (i + 1))) :
    polygon φ c N t = node φ c N i + (t - mesh N i) • slope φ c N i := by
  let term := fun j => ramp N j t • slope φ c N j
  have hb (j : ℕ) (hj : j < i) : term j = (N : ℝ)⁻¹ • slope φ c N j := by
    dsimp [term]
    rw [ramp_after ((mesh_mono (by omega : j + 1 ≤ i)).trans ht.1)]
  have ha (j : ℕ) (hj : i < j) : term j = 0 := by
    dsimp [term]
    rw [ramp_before (ht.2.trans (mesh_mono (by omega : i + 1 ≤ j))), zero_smul]
  have hsum : (∑ j ∈ Finset.range N, term j) =
      (∑ j ∈ Finset.range i, term j) + term i := by
    rw [← Finset.sum_range_succ]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : i + 1 ≤ N))
    intro j hj hj'
    exact ha j (by simp only [Finset.mem_range] at hj'; omega)
  unfold polygon
  change c + (∑ j ∈ Finset.range N, term j) = _
  rw [hsum, Finset.sum_congr rfl (fun j hj => hb j (Finset.mem_range.mp hj)), node_sum]
  dsimp [term]
  rw [ramp_cell ht]
  abel

lemma polygon_mesh (φ : ℝ → E → E) (c : E) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    polygon φ c N (mesh N i) = node φ c N i := by
  rcases hi.eq_or_lt with rfl | hi
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
    rw [polygon_cell φ c (by omega : j < j + 1) ⟨mesh_mono (Nat.le_succ j), le_rfl⟩,
      mesh_step, node_succ]
    rfl
  · rw [polygon_cell φ c hi ⟨le_rfl, mesh_mono (Nat.le_succ i)⟩, sub_self, zero_smul, add_zero]

/-- The source slope equation, away from mesh points. -/
lemma polygon_hasDerivAt (φ : ℝ → E → E) (c : E) {N i : ℕ} (hi : i < N)
    {t : ℝ} (ht : t ∈ Ioo (mesh N i) (mesh N (i + 1))) :
    HasDerivAt (polygon φ c N) (φ (mesh N i) (polygon φ c N (mesh N i))) t := by
  rw [polygon_mesh φ c (by omega) hi.le]
  have hd : HasDerivAt (fun s : ℝ => node φ c N i + (s - mesh N i) • slope φ c N i)
      (slope φ c N i) t := by
    simpa using (((hasDerivAt_id t).sub_const (mesh N i)).smul_const (slope φ c N i)).const_add (node φ c N i)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact polygon_cell φ c hi ⟨hs.1.le, hs.2.le⟩

lemma polygon_norm_sub_le {φ : ℝ → E → E} {c : E} {N : ℕ} (hN : 0 < N)
    {M : ℝ} (_hM : 0 ≤ M) (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖polygon φ c N t - polygon φ c N s‖ ≤ M * |t - s| := by
  suffices h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      ‖polygon φ c N t - polygon φ c N s‖ ≤ M * (t - s) by
    rcases le_total s t with hst | hts
    · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using h s hs t ht hst
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      exact h t ht s hs hts
  intro s hs t ht hst
  have he : polygon φ c N t - polygon φ c N s =
      ∑ i ∈ Finset.range N, (ramp N i t - ramp N i s) • slope φ c N i := by
    simp only [polygon, add_sub_add_left_eq_sub, sub_smul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖(ramp N i t - ramp N i s) • slope φ c N i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, (ramp N i t - ramp N i s) * M := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (ramp_monotone N i hst))]
      exact mul_le_mul_of_nonneg_left (hb _ (mesh_mem hN (Finset.mem_range.mp hi).le) _)
        (sub_nonneg.mpr (ramp_monotone N i hst))
    _ = M * (t - s) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_ramp_on hN ht, sum_ramp_on hN hs, mul_comm]

lemma polygon_bound {φ : ℝ → E → E} {c : E} {N : ℕ} (hN : 0 < N)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖polygon φ c N t‖ ≤ ‖c‖ + M := by
  have h := polygon_norm_sub_le (c := c) hN hM hb (left_mem_Icc.mpr zero_le_one) ht
  rw [polygon_zero, sub_zero, abs_of_nonneg ht.1] at h
  calc
    _ ≤ ‖polygon φ c N t - c‖ + ‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (polygon φ c N t - c) c
    _ ≤ ‖c‖ + M := by nlinarith [ht.2]

/-- The finite set of mesh points, including both endpoints. -/
def meshSet (N : ℕ) : Set ℝ := mesh N '' Iic N

lemma meshSet_finite (N : ℕ) : (meshSet N).Finite := (finite_Iic N).image _

lemma mesh_mem_meshSet {N i : ℕ} (hi : i ≤ N) : mesh N i ∈ meshSet N := ⟨i, hi, rfl⟩

lemma exists_cell {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i < N, t ∈ Icc (mesh N i) (mesh N (i + 1)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases he : t = 1
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
    refine ⟨i, by omega, ?_⟩
    rw [he, mesh_last (by omega : 0 < i + 1)]
    exact ⟨(mesh_mem (by omega) (Nat.le_succ i)).2, le_rfl⟩
  · have ht1 : t < 1 := lt_of_le_of_ne ht.2 he
    refine ⟨⌊t * N⌋₊, ?_, ?_, ?_⟩
    · apply (Nat.floor_lt (mul_nonneg ht.1 hn.le)).mpr
      nlinarith
    · apply (div_le_iff₀ hn).mpr
      exact Nat.floor_le (mul_nonneg ht.1 hn.le)
    · apply (le_div_iff₀ hn).mpr
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (t * N)).le

lemma exists_open_cell {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hm : t ∉ meshSet N) :
    ∃ i < N, t ∈ Ioo (mesh N i) (mesh N (i + 1)) := by
  obtain ⟨i, hi, hl, hu⟩ := exists_cell hN ht
  refine ⟨i, hi, lt_of_le_of_ne hl ?_, lt_of_le_of_ne hu ?_⟩
  · intro he
    exact hm (he ▸ mesh_mem_meshSet hi.le)
  · intro he
    exact hm (he.symm ▸ mesh_mem_meshSet (by omega))

/-- The step velocity; its endpoint values do not affect its integral. -/
def velocity (φ : ℝ → E → E) (c : E) (N : ℕ) (t : ℝ) : E :=
  ∑ i ∈ Finset.range N, (Ioc (mesh N i) (mesh N (i + 1))).indicator
    (fun _ => slope φ c N i) t

lemma velocity_cell (φ : ℝ → E → E) (c : E) {N i : ℕ} (hi : i < N)
    {t : ℝ} (ht : t ∈ Ioc (mesh N i) (mesh N (i + 1))) :
    velocity φ c N t = slope φ c N i := by
  unfold velocity
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j hj hji
    apply indicator_of_notMem
    intro hjt
    rcases lt_or_gt_of_ne hji with hji | hij
    · have hle : mesh N (j + 1) ≤ mesh N i := mesh_mono (by omega)
      linarith [hjt.2, ht.1]
    · have hle : mesh N (i + 1) ≤ mesh N j := mesh_mono (by omega)
      linarith [ht.2, hjt.1]
  · simp [Finset.mem_range, hi]

lemma velocity_continuousAt (φ : ℝ → E → E) (c : E) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hm : t ∉ meshSet N) :
    ContinuousAt (velocity φ c N) t := by
  obtain ⟨i, hi, hit⟩ := exists_open_cell hN ht hm
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hit.1 hit.2] with s hs
  exact velocity_cell φ c hi ⟨hs.1, hs.2.le⟩

/-- The residual is exactly zero at every mesh point. -/
def residual (φ : ℝ → E → E) (c : E) (N : ℕ) (t : ℝ) : E := by
  classical
  exact if t ∈ meshSet N then 0 else velocity φ c N t - φ t (polygon φ c N t)

@[simp] lemma residual_mesh (φ : ℝ → E → E) (c : E) {N i : ℕ} (hi : i ≤ N) :
    residual φ c N (mesh N i) = 0 := by
  simp [residual, mesh_mem_meshSet hi]

lemma residual_eq_deriv_sub (φ : ℝ → E → E) (c : E) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hm : t ∉ meshSet N) :
    residual φ c N t = deriv (polygon φ c N) t - φ t (polygon φ c N t) := by
  obtain ⟨i, hi, hit⟩ := exists_open_cell hN ht hm
  rw [residual, ite_eq_right hm, velocity_cell φ c hi ⟨hit.1, hit.2.le⟩,
    (polygon_hasDerivAt φ c hi hit).deriv, polygon_mesh φ c hN hi.le]
  rfl

lemma residual_bound {φ : ℝ → E → E} {c : E} {N : ℕ} (hN : 0 < N)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖residual φ c N t‖ ≤ 2 * M := by
  by_cases hm : t ∈ meshSet N
  · simp [residual, hm, hM]
  · obtain ⟨i, hi, hit⟩ := exists_open_cell hN ht hm
    rw [residual, ite_eq_right hm, velocity_cell φ c hi ⟨hit.1, hit.2.le⟩]
    exact (norm_sub_le _ _).trans (by
      dsimp only [slope]
      linarith [hb _ (mesh_mem hN hi.le) (node φ c N i), hb t ht (polygon φ c N t)])

lemma composition_continuousOn {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : E) (N : ℕ) : ContinuousOn (fun t => φ t (polygon φ c N t)) (Icc (0 : ℝ) 1) := by
  exact hc.comp (continuous_id.prodMk (polygon_continuous φ c N)).continuousOn
    (fun t ht => ⟨ht, mem_univ _⟩)

lemma residual_continuousWithinAt {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : E) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hm : t ∉ meshSet N) : ContinuousWithinAt (residual φ c N) (Icc (0 : ℝ) 1) t := by
  have h := (velocity_continuousAt φ c hN ht hm).continuousWithinAt.sub
    (composition_continuousOn hc c N t ht)
  apply h.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds
      ((meshSet_finite N).isClosed.isOpen_compl.mem_nhds hm)] with s hs
    simp only [residual, ite_eq_right hs, Pi.sub_apply]
  · simp only [residual, ite_eq_right hm, Pi.sub_apply]

lemma residual_ae_eq (φ : ℝ → E → E) (c : E) (N : ℕ) :
    residual φ c N =ᵐ[volume] fun t => velocity φ c N t - φ t (polygon φ c N t) := by
  filter_upwards [(meshSet_finite N).countable.ae_notMem volume] with t ht
  simp [residual, ht]

lemma velocity_integrable (φ : ℝ → E → E) (c : E) (N : ℕ) :
    Integrable (velocity φ c N) volume := by
  apply integrable_finsetSum
  intro i hi
  exact (integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc

lemma residual_intervalIntegrable {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : E) (N : ℕ) : IntervalIntegrable (residual φ c N) volume 0 1 := by
  have hi := (velocity_integrable φ c N).intervalIntegrable.sub
    ((composition_continuousOn hc c N).intervalIntegrable_of_Icc zero_le_one)
  exact hi.congr_ae (ae_restrict_of_ae (residual_ae_eq φ c N).symm)

/-- The residual is Riemann integrable, in the project's closed-cell Darboux sense. -/
theorem residual_riemann_integrable {φ : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : ℝ) {N : ℕ} (hN : 0 < N) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) :
    Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (residual φ c N) id 0 1
      (∫ t in (0 : ℝ)..1, residual φ c N t) := by
  apply Rudin.Support.RiemannIntegrability.hasDarbouxRSIntegral_of_ae_continuousWithinAt zero_le_one
    (fun t ht => by simpa only [Real.norm_eq_abs] using residual_bound (c := c) hN hM hb ht)
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae ((meshSet_finite N).countable.ae_notMem volume)] with t ht hm
  exact residual_continuousWithinAt hc c hN ht hm

lemma polygon_lipschitz {φ : ℝ → E → E} {c : E} {N : ℕ} (hN : 0 < N)
    {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) :
    LipschitzWith M (polygon φ c N) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [dist_eq_norm, Real.dist_eq]
  suffices h : ∀ s t : ℝ, s ≤ t → ‖polygon φ c N t - polygon φ c N s‖ ≤ M * (t - s) by
    rcases le_total s t with hst | hts
    · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using h s t hst
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      exact h t s hts
  intro s t hst
  have he : polygon φ c N t - polygon φ c N s =
      ∑ i ∈ Finset.range N, (ramp N i t - ramp N i s) • slope φ c N i := by
    simp only [polygon, add_sub_add_left_eq_sub, sub_smul, Finset.sum_sub_distrib]
  have hh : (min t 1 - min t 0) - (min s 1 - min s 0) ≤ t - s := by
    simp only [min_def]
    split_ifs <;> linarith
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖(ramp N i t - ramp N i s) • slope φ c N i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, (ramp N i t - ramp N i s) * M := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (ramp_monotone N i hst))]
      exact mul_le_mul_of_nonneg_left (hb _ (mesh_mem hN (Finset.mem_range.mp hi).le) _)
        (sub_nonneg.mpr (ramp_monotone N i hst))
    _ ≤ M * (t - s) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_ramp, sum_ramp, mesh_last hN, mul_comm]
      exact mul_le_mul_of_nonneg_left hh M.coe_nonneg

/-- In particular every actual polygon derivative has the stated bound. -/
lemma polygon_deriv_bound {φ : ℝ → E → E} {c : E} {N : ℕ} (hN : 0 < N)
    {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) (t : ℝ) :
    ‖deriv (polygon φ c N) t‖ ≤ M :=
  norm_deriv_le_of_lipschitz (polygon_lipschitz hN hb)

/-- The Euler family is equicontinuous, even on the full real line. -/
theorem polygon_equicontinuous {φ : ℝ → E → E} (c : E)
    {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) :
    Equicontinuous (fun n : ℕ => polygon φ c (n + 1)) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => M * r)
    (by simpa using (tendsto_const_nhds (x := (M : ℝ))).mul (tendsto_id (x := 𝓝 (0 : ℝ))))
  intro s t n
  exact (polygon_lipschitz (Nat.succ_pos n) hb).dist_le_mul s t

variable [CompleteSpace E]

lemma integral_indicator_cell {l u t : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (ht : 0 ≤ t)
    (v : E) :
    (∫ s in (0 : ℝ)..t, (Ioc l u).indicator (fun _ => v) s) =
      (min t u - min t l) • v := by
  rw [intervalIntegral.integral_of_le ht, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc,
    setIntegral_const, Real.volume_real_Ioc]
  congr 1
  rw [max_eq_left hl, min_comm u t]
  by_cases htl : t ≤ l
  · rw [min_eq_left (htl.trans hlu), min_eq_left htl, sub_self,
      max_eq_right (sub_nonpos.mpr htl)]
  · have hlt : l ≤ t := (lt_of_not_ge htl).le
    rw [min_eq_right hlt, max_eq_left (sub_nonneg.mpr (le_min hlt hlu))]

lemma velocity_integral (φ : ℝ → E → E) (c : E) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, velocity φ c N s) = polygon φ c N t - c := by
  rw [show velocity φ c N = fun t => ∑ i ∈ Finset.range N,
    (Ioc (mesh N i) (mesh N (i + 1))).indicator (fun _ => slope φ c N i) t from rfl,
    intervalIntegral.integral_finsetSum]
  · simp only [integral_indicator_cell (by unfold mesh; positivity)
      (mesh_mono (Nat.le_succ _)) ht, polygon, ramp, add_sub_cancel_left]
  · intro i hi
    exact ((integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc).intervalIntegrable

/-- The residual identity, with actual integrability of the integrand. -/
theorem residual_integral_identity {φ : ℝ → E → E}
    (_hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : E) (N : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => φ t (polygon φ c N t) + residual φ c N t) volume 0 x ∧
    polygon φ c N x = c + ∫ t in (0 : ℝ)..x, φ t (polygon φ c N t) + residual φ c N t := by
  have he : (fun t => φ t (polygon φ c N t) + residual φ c N t) =ᵐ[volume] velocity φ c N := by
    filter_upwards [residual_ae_eq φ c N] with t ht
    rw [ht]
    abel
  constructor
  · exact (velocity_integrable φ c N).intervalIntegrable.congr_ae (ae_restrict_of_ae he.symm)
  · rw [intervalIntegral.integral_congr_ae (he.mono fun t ht _ => ht), velocity_integral φ c N hx.1]
    abel

/-- The same residual identity as an ordinary Riemann integral, with the bridge proved. -/
theorem residual_riemann_identity {φ : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : ℝ) {N : ℕ} (hN : 0 < N) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral
      (fun t => φ t (polygon φ c N t) + residual φ c N t) id 0 x (polygon φ c N x - c) := by
  have hi := (residual_integral_identity hc c N hx).2
  have he : (∫ t in (0 : ℝ)..x, φ t (polygon φ c N t) + residual φ c N t) = polygon φ c N x - c := by
    linarith
  rw [← he]
  apply Rudin.Support.RiemannIntegrability.hasDarbouxRSIntegral_of_ae_continuousWithinAt hx.1
    (M := 3 * M)
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
    exact (abs_add_le _ _).trans (by
      have h := residual_bound (c := c) hN hM hb ht'
      simp only [Real.norm_eq_abs] at h
      have h' := hb t ht' (polygon φ c N t)
      simp only [Real.norm_eq_abs] at h'
      linarith)
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae ((meshSet_finite N).countable.ae_notMem volume)] with t ht hm
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
    exact ((composition_continuousOn hc c N t ht').add
      (residual_continuousWithinAt hc c hN ht' hm)).mono (Icc_subset_Icc le_rfl hx.2)

variable [ProperSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma field_uniformContinuousOn {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ)) (R : ℝ) :
    UniformContinuousOn (fun p : ℝ × E => φ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : E) R) :=
  (isCompact_Icc.prod (isCompact_closedBall 0 R)).uniformContinuousOn_of_continuous
    (hc.mono (prod_mono Subset.rfl (subset_univ _)))

omit [CompleteSpace E] in
/-- The full residual sequence tends uniformly to zero, not just a subsequence. -/
theorem residual_uniform {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : E) {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) :
    TendstoUniformlyOn (fun n => residual φ c (n + 1)) (fun _ => 0) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (field_uniformContinuousOn hc (‖c‖ + M)) ε hε
  have hz : Tendsto (fun n : ℕ => (1 + (M : ℝ)) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := (1 + (M : ℝ)))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [hz.eventually (gt_mem_nhds hδ)] with n hn t ht
  by_cases hm : t ∈ meshSet (n + 1)
  · simpa [residual, hm] using hε
  · obtain ⟨i, hi, hit⟩ := exists_open_cell (Nat.succ_pos n) ht hm
    have hmesh := mesh_mem (Nat.succ_pos n) hi.le
    have hpt := polygon_bound (c := c) (Nat.succ_pos n) M.coe_nonneg hb ht
    have hpi := polygon_bound (c := c) (Nat.succ_pos n) M.coe_nonneg hb hmesh
    have hstep : |t - mesh (n + 1) i| ≤ ((n : ℝ) + 1)⁻¹ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hit.1.le)]
      have hh := mesh_step (n + 1) i
      push_cast at hh
      linarith [hit.2]
    have hdistance : dist (mesh (n + 1) i, polygon φ c (n + 1) (mesh (n + 1) i))
        (t, polygon φ c (n + 1) t) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq, abs_sub_comm]
        apply lt_of_le_of_lt hstep
        apply lt_of_le_of_lt _ hn
        have hp : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
        rw [div_eq_mul_inv]
        nlinarith [M.coe_nonneg]
      · rw [dist_eq_norm, norm_sub_rev]
        apply lt_of_le_of_lt (polygon_norm_sub_le (Nat.succ_pos n) M.coe_nonneg hb hmesh ht)
        apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hstep M.coe_nonneg)
        apply lt_of_le_of_lt _ hn
        rw [div_eq_mul_inv]
        nlinarith [show 0 ≤ ((n : ℝ) + 1)⁻¹ by positivity]
    have hv := hd _ ⟨hmesh, by simpa [Metric.mem_closedBall, dist_zero_right] using hpi⟩
      _ ⟨ht, by simpa [Metric.mem_closedBall, dist_zero_right] using hpt⟩ hdistance
    rw [residual, ite_eq_right hm, velocity_cell φ c hi ⟨hit.1, hit.2.le⟩]
    simpa only [Pi.zero_apply, dist_zero_left, zero_sub, norm_neg, slope,
      polygon_mesh φ c (Nat.succ_pos n) hi.le, dist_eq_norm] using hv

omit [CompleteSpace E] [ProperSpace E] in
lemma limit_bound {φ : ℝ → E → E} {c : E} {M : ℝ≥0}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) {σ : ℕ → ℕ} {f : ℝ → E}
    (hu : TendstoUniformlyOn (fun n => polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖f t‖ ≤ ‖c‖ + M :=
  le_of_tendsto ((hu.tendsto_at ht).norm)
    (Eventually.of_forall fun _n => polygon_bound (Nat.succ_pos _) M.coe_nonneg hb ht)

omit [CompleteSpace E] in
/-- Uniform continuity on the compact rectangle transfers the uniform polygon limit. -/
theorem composition_uniform {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    {c : E} {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {σ : ℕ → ℕ} {f : ℝ → E}
    (hu : TendstoUniformlyOn (fun n => polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1)) :
    TendstoUniformlyOn (fun n t => φ t (polygon φ c (σ n + 1) t))
      (fun t => φ t (f t)) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff] at ⊢
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (field_uniformContinuousOn hc (‖c‖ + M)) ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) δ hδ] with n hn t ht
  apply hd (t, f t) ⟨ht, by
    simpa [Metric.mem_closedBall, dist_zero_right] using limit_bound hb hu ht⟩
    (t, polygon φ c (σ n + 1) t) ⟨ht, by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        polygon_bound (c := c) (Nat.succ_pos (σ n)) M.coe_nonneg hb ht⟩
  simpa [Prod.dist_eq] using hn t ht

/-- Every uniformly convergent Euler subsequence satisfies the integral equation. -/
theorem limit_integral_equation {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    {c : E} {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℝ → E}
    (hu : TendstoUniformlyOn (fun n => polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x = c + ∫ t in (0 : ℝ)..x, φ t (f t) := by
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) := hu.continuousOn
    (Frequently.of_forall fun n => (polygon_continuous φ c (σ n + 1)).continuousOn)
  have hg : ContinuousOn (fun t => φ t (f t)) (Icc (0 : ℝ) 1) :=
    hc.comp (continuousOn_id.prodMk hf) (fun t ht => ⟨ht, mem_univ _⟩)
  have hr : TendstoUniformlyOn (fun n => residual φ c (σ n + 1)) (fun _ => 0)
      atTop (Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact hσ.tendsto_atTop.eventually ((Metric.tendstoUniformlyOn_iff.mp (residual_uniform hc c hb)) ε hε)
  have hg' : TendstoUniformlyOn
      (fun n t => φ t (polygon φ c (σ n + 1) t) + residual φ c (σ n + 1) t)
      (fun t => φ t (f t)) atTop (Icc (0 : ℝ) 1) := by
    have h := (composition_uniform hc hb hu).add hr
    change TendstoUniformlyOn
      (fun n t => φ t (polygon φ c (σ n + 1) t) + residual φ c (σ n + 1) t)
      (fun t => φ t (f t) + 0) atTop (Icc (0 : ℝ) 1) at h
    simpa only [add_zero] using h
  have hi := Rudin.Support.UniformIntegralLimits.uniform_primitives
    (fun n x hx => (residual_integral_identity hc c (σ n + 1) hx).1)
    (fun x hx => (hg.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1) hg'
  apply tendsto_nhds_unique (hu.tendsto_at hx)
  have hl := (tendsto_const_nhds (x := c)).add (hi.tendsto_at hx)
  exact hl.congr (fun n => (residual_integral_identity hc c (σ n + 1) hx).2.symm)

/-- The uniform Euler limit has the initial value and genuine one-sided endpoint derivatives. -/
theorem limit_solution {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    {c : E} {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℝ → E}
    (hu : TendstoUniformlyOn (fun n => polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1)) :
    f 0 = c ∧ ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (φ x (f x)) (Icc (0 : ℝ) 1) x := by
  have he := fun x hx => limit_integral_equation hc hb hσ hu (x := x) hx
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) := hu.continuousOn
    (Frequently.of_forall fun n => (polygon_continuous φ c (σ n + 1)).continuousOn)
  have hg : ContinuousOn (fun t => φ t (f t)) (Icc (0 : ℝ) 1) :=
    hc.comp (continuousOn_id.prodMk hf) (fun t ht => ⟨ht, mem_univ _⟩)
  constructor
  · simpa using he 0 (left_mem_Icc.mpr zero_le_one)
  · intro x hx
    exact ((Rudin.Support.UniformIntegralLimits.primitive_hasDerivWithinAt hg hx).const_add c).congr he (he x hx)

omit [CompleteSpace E] in
/-- Actual Ascoli selection from the constructed Euler sequence. -/
theorem polygon_subsequence {φ : ℝ → E → E} (c : E) {M : ℝ≥0}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) :
    ∃ f : ℝ → E, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n => polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1) := by
  classical
  let K := Icc (0 : ℝ) 1
  let F : ℕ → K → E := fun n t => polygon φ c (n + 1) t
  have he : Equicontinuous F := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => M * r)
      (by simpa using (tendsto_const_nhds (x := (M : ℝ))).mul (tendsto_id (x := 𝓝 (0 : ℝ))))
    intro s t n
    exact (polygon_lipschitz (Nat.succ_pos n) hb).dist_le_mul s.val t.val
  have hbd (t : K) : Bornology.IsBounded (range (fun n => F n t)) := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := ‖c‖ + M)).subset
    rintro _ ⟨n, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      polygon_bound (c := c) (Nat.succ_pos n) M.coe_nonneg hb t.property
  obtain ⟨g, _, σ, hσ, hu⟩ := Rudin.Chapter07.exercise17_vector_selection_subsequence he hbd
  let f : ℝ → E := fun t => if ht : t ∈ K then g ⟨t, ht⟩ else c
  refine ⟨f, σ, hσ, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with n hn t ht
  have htk : t ∈ K := ht
  simpa [f, htk, F] using hn ⟨t, ht⟩

/-- The complete polygon construction produces an integral and differential solution. -/
theorem exists_solution {φ : ℝ → E → E}
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (c : E) {M : ℝ≥0} (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖φ t z‖ ≤ M) :
    ∃ f : ℝ → E, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n => polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1) ∧
      ContinuousOn f (Icc (0 : ℝ) 1) ∧ f 0 = c ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f x = c + ∫ t in (0 : ℝ)..x, φ t (f t)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (φ x (f x)) (Icc (0 : ℝ) 1) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (φ x (f x)) x) := by
  obtain ⟨f, σ, hσ, hu⟩ := polygon_subsequence c hb
  have hs := limit_solution hc hb hσ hu
  refine ⟨f, σ, hσ, hu, hu.continuousOn
    (Frequently.of_forall fun n => (polygon_continuous φ c (σ n + 1)).continuousOn), hs.1,
    fun x hx => limit_integral_equation hc hb hσ hu hx, hs.2, ?_⟩
  intro x hx
  exact (hs.2 x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

end Rudin.Chapter07.Euler

namespace Rudin.Chapter07

/-- The scalar source theorem, with its Euler subsequence and endpoint derivatives. -/
theorem exercise25_solution (φ : ℝ → ℝ → ℝ) (c : ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hb : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, |φ t z| ≤ M) :
    ∃ f : ℝ → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n => Euler.polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1) ∧
      ContinuousOn f (Icc (0 : ℝ) 1) ∧ f 0 = c ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f x = c + ∫ t in (0 : ℝ)..x, φ t (f t)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (φ x (f x)) (Icc (0 : ℝ) 1) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (φ x (f x)) x) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (left_mem_Icc.mpr zero_le_one) c)
  exact Euler.exists_solution hc c (M := ⟨M, hM0⟩)
    (fun t ht z => by change |φ t z| ≤ M; exact hM t ht z)

/-- The scalar limit equation is also the literal ordinary Riemann integral equation. -/
theorem exercise25_riemann_solution (φ : ℝ → ℝ → ℝ) (c : ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hb : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, |φ t z| ≤ M) :
    ∃ f : ℝ → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n => Euler.polygon φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1) ∧
      ContinuousOn f (Icc (0 : ℝ) 1) ∧ f 0 = c ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral (fun t => φ t (f t)) id 0 x (f x - c)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (φ x (f x)) (Icc (0 : ℝ) 1) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (φ x (f x)) x) := by
  obtain ⟨f, σ, hσ, hu, hf, hf0, he, hd, hdi⟩ := exercise25_solution φ c hc hb
  refine ⟨f, σ, hσ, hu, hf, hf0, ?_, hd, hdi⟩
  intro x hx
  have hg : ContinuousOn (fun t => φ t (f t)) (Icc (0 : ℝ) 1) :=
    hc.comp (continuousOn_id.prodMk hf) (fun t ht => ⟨ht, mem_univ _⟩)
  obtain ⟨M, hM⟩ := hb
  have hR := Rudin.Support.RiemannIntegrability.hasDarbouxRSIntegral_of_ae_continuousWithinAt hx.1
    (fun t (ht : t ∈ Icc (0 : ℝ) x) => hM t ⟨ht.1, ht.2.trans hx.2⟩ (f t))
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht =>
      (hg.mono (Icc_subset_Icc le_rfl hx.2)) t ht))
  have hi : (∫ t in (0 : ℝ)..x, φ t (f t)) = f x - c := by linarith [he x hx]
  rwa [hi] at hR

end Rudin.Chapter07
