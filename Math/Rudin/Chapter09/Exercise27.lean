module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Tactic

/-! # R09E27: unequal mixed partial derivatives
Book page 242, PDF page 251. Coordinates are represented by `ℝ × ℝ`.
Division gives the prescribed value zero at the origin.
The order D12 means D1(D2 f), as in Rudin.
-/
@[expose] public section
namespace Rudin.Chapter09
open Filter Topology

noncomputable def exercise27f (x y : ℝ) : ℝ := x*y*(x^2-y^2)/(x^2+y^2)
noncomputable def exercise27P (x y : ℝ) : ℝ :=
  y*(x^4+4*x^2*y^2-y^4)/(x^2+y^2)^2
noncomputable def exercise27Q (x y : ℝ) : ℝ := -exercise27P y x
noncomputable def exercise27K (x y : ℝ) : ℝ :=
  (x^6+9*x^4*y^2-9*x^2*y^4-y^6)/(x^2+y^2)^3

@[simp] theorem exercise27_zero : exercise27f 0 0 = 0 := by simp [exercise27f]

theorem exercise27_den {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) : x^2+y^2 ≠ 0 := by
  intro hz
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  rcases h with h | h <;> contradiction

theorem exercise27_swap (x y : ℝ) : exercise27f x y = -exercise27f y x := by
  unfold exercise27f
  rw [add_comm (y^2) (x^2)]
  ring

@[simp] theorem exercise27_axis (x : ℝ) : exercise27P 0 x = -x := by
  by_cases hx : x = 0
  · simp [hx, exercise27P]
  · unfold exercise27P; field_simp; ring

theorem exercise27_first (x y : ℝ) :
    HasDerivAt (fun s => exercise27f s y) (exercise27P x y) x := by
  by_cases hy : y = 0
  · subst y
    simpa [exercise27f, exercise27P] using hasDerivAt_const x (0 : ℝ)
  · have hd := exercise27_den (x := x) (Or.inr hy)
    convert (((hasDerivAt_id x).mul_const y).mul
      (((hasDerivAt_id x).pow 2).sub_const (y^2))).div
      (((hasDerivAt_id x).pow 2).add_const (y^2)) hd using 1
    · rfl
    · dsimp [exercise27P]; field_simp; ring

theorem exercise27_second (x y : ℝ) :
    HasDerivAt (fun s => exercise27f x s) (exercise27Q x y) y := by
  have he : (fun s => exercise27f x s) = fun s => -exercise27f s x :=
    funext (exercise27_swap x)
  rw [he]
  exact (exercise27_first y x).neg

theorem exercise27_P_bound (x y : ℝ) : |exercise27P x y| ≤ 3*|y| := by
  by_cases h : x = 0 ∧ y = 0
  · rcases h with ⟨rfl,rfl⟩; simp [exercise27P]
  have hd := exercise27_den (show x ≠ 0 ∨ y ≠ 0 from not_and_or.mp h)
  have hn : |x^4+4*x^2*y^2-y^4| ≤ 3*(x^2+y^2)^2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x^2), sq_nonneg (y^2),
      mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  rw [exercise27P, abs_div, abs_mul, abs_of_pos (sq_pos_of_ne_zero hd),
    div_le_iff₀ (sq_pos_of_ne_zero hd)]
  nlinarith [mul_le_mul_of_nonneg_left hn (abs_nonneg y)]

theorem exercise27_P_continuous : Continuous (fun p : ℝ × ℝ => exercise27P p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = (0,0)
  · subst p
    change Tendsto _ _ (𝓝 (exercise27P 0 0))
    simp only [exercise27_axis, neg_zero]
    apply squeeze_zero_norm (fun q : ℝ × ℝ => exercise27_P_bound q.1 q.2)
    convert ((continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)).abs.const_mul (3 : ℝ)).continuousAt.tendsto (x := (0,0)) using 1
    simp
  · have hd : p.1^2+p.2^2 ≠ 0 := exercise27_den (by
      by_contra h; push Not at h; exact hp (Prod.ext h.1 h.2))
    unfold exercise27P
    fun_prop (disch := exact pow_ne_zero 2 hd)

theorem exercise27_first_partials :
    (∀ x y, HasDerivAt (fun s => exercise27f s y) (exercise27P x y) x ∧
      HasDerivAt (fun s => exercise27f x s) (exercise27Q x y) y) ∧
    Continuous (fun p : ℝ × ℝ => exercise27P p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => exercise27Q p.1 p.2) := by
  exact ⟨fun x y => ⟨exercise27_first x y, exercise27_second x y⟩,
    exercise27_P_continuous, (exercise27_P_continuous.comp continuous_swap).neg⟩

theorem exercise27_f_bound (x y : ℝ) : |exercise27f x y| ≤ |x| * |y| := by
  by_cases h : x = 0 ∧ y = 0
  · rcases h with ⟨rfl,rfl⟩; simp
  have hd := exercise27_den (show x ≠ 0 ∨ y ≠ 0 from not_and_or.mp h)
  have hdpos : 0 < x^2+y^2 := lt_of_le_of_ne (by positivity) (Ne.symm hd)
  rw [exercise27f, abs_div, abs_mul, abs_mul, abs_of_pos hdpos, div_le_iff₀ hdpos]
  exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]) (by positivity)

theorem exercise27_continuous : Continuous (fun p : ℝ × ℝ => exercise27f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = (0,0)
  · subst p
    change Tendsto _ _ (𝓝 (exercise27f 0 0))
    rw [exercise27_zero]
    apply squeeze_zero_norm (fun q : ℝ × ℝ => exercise27_f_bound q.1 q.2)
    convert (((continuous_fst : Continuous (fun p : ℝ × ℝ => p.1)).abs).mul
      (continuous_snd.abs)).continuousAt.tendsto (x := (0,0)) using 1
    simp
  · have hd : p.1^2+p.2^2 ≠ 0 := exercise27_den (by
      by_contra h; push Not at h; exact hp (Prod.ext h.1 h.2))
    unfold exercise27f
    fun_prop (disch := exact hd)

/-- A genuine derivative of the first partial, including the entire vertical axis. -/
theorem exercise27_mixed21 (x y : ℝ) :
    HasDerivAt (fun s => exercise27P x s)
      (if x = 0 ∧ y = 0 then -1 else exercise27K x y) y := by
  by_cases hx : x = 0
  · subst x
    have he : (fun s => exercise27P 0 s) = fun s : ℝ => -s := funext exercise27_axis
    rw [he]
    convert (hasDerivAt_id y).neg using 1
    · rfl
    · split_ifs with h
      · rfl
      · have hy : y ≠ 0 := by simpa using h
        dsimp [exercise27K]; field_simp; ring
  · have hd := exercise27_den (y := y) (Or.inl hx)
    have h := ((hasDerivAt_id y).mul
      (((hasDerivAt_const y (x^4)).add (((hasDerivAt_id y).pow 2).const_mul (4*x^2))).sub
        ((hasDerivAt_id y).pow 4))).div
      ((((hasDerivAt_id y).pow 2).const_add (x^2)).pow 2) (pow_ne_zero 2 hd)
    convert h using 1
    · rfl
    · simp only [hx, false_and, ↓reduceIte]
      dsimp [exercise27K]
      field_simp
      ring

theorem exercise27_mixed12 (x y : ℝ) :
    HasDerivAt (fun s => exercise27Q s y)
      (if x = 0 ∧ y = 0 then 1 else -exercise27K y x) x := by
  convert (exercise27_mixed21 y x).neg using 1
  · rfl
  · by_cases h : x = 0 ∧ y = 0
    · simp [h.1, h.2]
    · have h' : ¬ (y = 0 ∧ x = 0) := fun hh => h ⟨hh.2,hh.1⟩
      simp [h,h']

/-- Mixed derivatives of the actual first derivatives, not total-derivative defaults. -/
theorem exercise27_mixed_existence (x y : ℝ) :
    (∃ a, HasDerivAt (fun s => deriv (fun t => exercise27f s t) y) a x) ∧
    (∃ b, HasDerivAt (fun t => deriv (fun s => exercise27f s t) x) b y) := by
  simp_rw [(exercise27_first _ _).deriv, (exercise27_second _ _).deriv]
  exact ⟨⟨_, exercise27_mixed12 x y⟩, ⟨_, exercise27_mixed21 x y⟩⟩

theorem exercise27_D12_zero :
    HasDerivAt (fun x => deriv (fun y => exercise27f x y) 0) 1 0 := by
  simp_rw [(exercise27_second _ _).deriv]
  simpa using exercise27_mixed12 0 0

theorem exercise27_D21_zero :
    HasDerivAt (fun y => deriv (fun x => exercise27f x y) 0) (-1) 0 := by
  simp_rw [(exercise27_first _ _).deriv]
  simpa using exercise27_mixed21 0 0

noncomputable def exercise27D12 (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => exercise27f x y) p.2) p.1
noncomputable def exercise27D21 (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => deriv (fun x => exercise27f x y) p.1) p.2

theorem exercise27_D21_formula (p : ℝ × ℝ) :
    exercise27D21 p = if p = (0,0) then -1 else exercise27K p.1 p.2 := by
  simp only [exercise27D21, (exercise27_first _ _).deriv]
  rw [(exercise27_mixed21 _ _).deriv]
  simp only [Prod.ext_iff]

theorem exercise27_D12_formula (p : ℝ × ℝ) :
    exercise27D12 p = if p = (0,0) then 1 else -exercise27K p.2 p.1 := by
  simp only [exercise27D12, (exercise27_second _ _).deriv]
  rw [(exercise27_mixed12 _ _).deriv]
  simp only [Prod.ext_iff]

theorem exercise27_K_continuousAt {p : ℝ × ℝ} (hp : p ≠ (0,0)) :
    ContinuousAt (fun q : ℝ × ℝ => exercise27K q.1 q.2) p := by
  have hd : p.1^2+p.2^2 ≠ 0 := exercise27_den (by
    by_contra h; push Not at h; exact hp (Prod.ext h.1 h.2))
  unfold exercise27K
  fun_prop (disch := exact pow_ne_zero 3 hd)

theorem exercise27_mixed_continuous_off_zero {p : ℝ × ℝ} (hp : p ≠ (0,0)) :
    ContinuousAt exercise27D12 p ∧ ContinuousAt exercise27D21 p := by
  have he : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q ≠ (0,0) :=
    (isOpen_compl_singleton.mem_nhds hp)
  constructor
  · have hs : (p.2,p.1) ≠ (0,0) := by
      intro h; exact hp (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
    have hh : ContinuousAt (fun q : ℝ × ℝ => -exercise27K q.2 q.1) p :=
      ((exercise27_K_continuousAt hs).comp (f := Prod.swap) continuous_swap.continuousAt).neg
    apply hh.congr_of_eventuallyEq
    filter_upwards [he] with q hq
    simp [exercise27_D12_formula, hq]
  · apply (exercise27_K_continuousAt hp).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    simp [exercise27_D21_formula, hq]

theorem exercise27_K_axis {x : ℝ} (hx : x ≠ 0) : exercise27K x 0 = 1 := by
  dsimp [exercise27K]; field_simp; ring

theorem exercise27_D21_axis {x : ℝ} (hx : x ≠ 0) : exercise27D21 (x,0) = 1 := by
  rw [exercise27_D21_formula, ite_eq_right (by simp [hx]), exercise27_K_axis hx]

theorem exercise27_D12_axis {y : ℝ} (hy : y ≠ 0) : exercise27D12 (0,y) = -1 := by
  rw [exercise27_D12_formula, ite_eq_right (by simp [hy]), exercise27_K_axis hy]

theorem exercise27_mixed_discontinuous :
    ¬ ContinuousAt exercise27D12 (0,0) ∧ ¬ ContinuousAt exercise27D21 (0,0) := by
  constructor
  · intro h
    have hc := h.comp (f := fun y : ℝ => ((0 : ℝ), y)) (by fun_prop)
    have ht : Tendsto (fun y : ℝ => exercise27D12 (0,y)) (𝓝[≠] 0) (𝓝 1) := by
      simpa only [Function.comp_def, exercise27_D12_formula, ite_true] using
        hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    have he : (fun y : ℝ => exercise27D12 (0,y)) =ᶠ[𝓝[≠] 0] fun _ => -1 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact exercise27_D12_axis hy
    have hh := tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)
    norm_num at hh
  · intro h
    have hc := h.comp (f := fun x : ℝ => (x, (0 : ℝ))) (by fun_prop)
    have ht : Tendsto (fun x : ℝ => exercise27D21 (x,0)) (𝓝[≠] 0) (𝓝 (-1)) := by
      simpa only [Function.comp_def, exercise27_D21_formula, ite_true] using
        hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    have he : (fun x : ℝ => exercise27D21 (x,0)) =ᶠ[𝓝[≠] 0] fun _ => 1 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact exercise27_D21_axis hx
    have hh := tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)
    norm_num at hh

/-- The continuous first partials give genuine C1 regularity on the plane. -/
theorem exercise27_C1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => exercise27f p.1 p.2) := by
  let A : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (exercise27P x y)
  let B : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (exercise27Q x y)
  have hA : Continuous (fun p : ℝ × ℝ => A p.1 p.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp exercise27_P_continuous
  have hB : Continuous (fun p : ℝ × ℝ => B p.1 p.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp exercise27_first_partials.2.2
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun p => (A p.1 p.2).coprod (B p.1 p.2), hA.continuousLinearMapCoprod hB, ?_⟩
  intro p
  exact (hasStrictFDerivAt_uncurry_coprod (u := p) (f := exercise27f) (f₁ := A) (f₂ := B)
    (Filter.Eventually.of_forall (fun q => (exercise27_first q.1 q.2).hasFDerivAt))
    (Filter.Eventually.of_forall (fun q => (exercise27_second q.1 q.2).hasFDerivAt))
    hA.continuousAt hB.continuousAt).hasFDerivAt

/-- The continuous fields above are exactly the coordinate derivatives. -/
theorem exercise27_actual_first_partials :
    Continuous (fun p : ℝ × ℝ => deriv (fun x => exercise27f x p.2) p.1) ∧
    Continuous (fun p : ℝ × ℝ => deriv (fun y => exercise27f p.1 y) p.2) := by
  simp_rw [(exercise27_first _ _).deriv, (exercise27_second _ _).deriv]
  exact exercise27_first_partials.2

theorem exercise27_mixed_values : exercise27D12 (0,0) = 1 ∧ exercise27D21 (0,0) = -1 :=
  ⟨exercise27_D12_zero.deriv, exercise27_D21_zero.deriv⟩

end Rudin.Chapter09
