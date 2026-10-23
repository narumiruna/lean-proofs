module

public import Mathlib

/-!
# Exercise 9.12

Source: Rudin, *Principles of Mathematical Analysis*, third edition,
book pages 239–240, PDF pages 248–249. The inverse image in (a) and (b)
is a fiber. The parameters are real, not restricted to a fundamental square.
The target carries the Euclidean norm.
-/

@[expose] public section
noncomputable section
open Set Real Filter
open scoped Topology
namespace Rudin.Chapter09.Exercise12

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)

def point (x y z : ℝ) : E3 := WithLp.toLp 2 ![x, y, z]
def torus (a b s t : ℝ) : E3 :=
  point ((b + a * cos s) * cos t) ((b + a * cos s) * sin t) (a * sin s)
def surface (a b : ℝ) : Set E3 :=
  {p | (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - b) ^ 2 + p 2 ^ 2 = a ^ 2}
def winding (a b l t : ℝ) : E3 := torus a b t (l * t)

@[simp] theorem point_zero (x y z : ℝ) : point x y z 0 = x := rfl
@[simp] theorem point_one (x y z : ℝ) : point x y z 1 = y := rfl
@[simp] theorem point_two (x y z : ℝ) : point x y z 2 = z := rfl

theorem radius_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) :
    0 < b + a * cos s := by
  nlinarith [neg_one_le_cos s]

theorem continuous_torus (a b : ℝ) : Continuous (fun u : ℝ × ℝ => torus a b u.1 u.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem polar {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) :
    ∃ t : ℝ, cos t = x ∧ sin t = y := by
  let z : ℂ := ⟨x, y⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    change Real.sqrt (x * x + y * y) = 1
    rw [← sq, ← sq, h, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at hn
  exact ⟨z.arg, by simpa [z, hn] using Complex.cos_arg hz,
    by simpa [z, hn] using Complex.sin_arg z⟩

theorem radial_identity (a b s t : ℝ) :
    (torus a b s t) 0 ^ 2 + (torus a b s t) 1 ^ 2 = (b + a * cos s) ^ 2 := by
  have h := cos_sq_add_sin_sq t
  dsimp [torus, point]
  nlinarith [sq_nonneg (b + a * cos s)]

theorem torus_mem_surface {a b : ℝ} (ha : 0 < a) (hab : a < b) (s t : ℝ) :
    torus a b s t ∈ surface a b := by
  change (Real.sqrt (_ ^ 2 + _ ^ 2) - b) ^ 2 + _ ^ 2 = _
  rw [radial_identity, Real.sqrt_sq (radius_pos ha hab s).le]
  dsimp [torus, point]
  nlinarith [sin_sq_add_cos_sq s]

/-- The usual ring torus equation, with no extra component or filled interior. -/
theorem range_eq_surface {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Set.range (fun u : ℝ × ℝ => torus a b u.1 u.2) = surface a b := by
  ext p
  constructor
  · rintro ⟨⟨s,t⟩, rfl⟩; exact torus_mem_surface ha hab s t
  · intro hp
    let r := Real.sqrt (p 0 ^ 2 + p 1 ^ 2)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = p 0 ^ 2 + p 1 ^ 2 := Real.sq_sqrt (by positivity)
    have he : (r - b) ^ 2 + p 2 ^ 2 = a ^ 2 := hp
    have hr : 0 < r := by nlinarith [sq_nonneg (p 2)]
    obtain ⟨s, hs, hs'⟩ := polar (x := (r-b)/a) (y := p 2/a) (by
      field_simp; nlinarith)
    obtain ⟨t, ht, ht'⟩ := polar (x := p 0/r) (y := p 1/r) (by
      field_simp; nlinarith)
    refine ⟨(s,t), ?_⟩
    ext i
    fin_cases i <;> simp [torus, point, hs, hs', ht, ht'] <;> field_simp <;> ring

theorem periodic_s (a b t : ℝ) : Function.Periodic (fun s => torus a b s t) (2 * π) := by
  intro s; simp [torus, cos_add_two_pi, sin_add_two_pi]
theorem periodic_t (a b s : ℝ) : Function.Periodic (torus a b s) (2 * π) := by
  intro t; simp [torus, cos_add_two_pi, sin_add_two_pi]

/-- Every real parameter pair has a representative in the closed period square. -/
theorem fundamental_square (a b : ℝ) :
    (fun u : ℝ × ℝ => torus a b u.1 u.2) ''
      (Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)) =
      Set.range (fun u : ℝ × ℝ => torus a b u.1 u.2) := by
  apply Subset.antisymm (image_subset_range _ _)
  rintro p ⟨⟨s,t⟩,rfl⟩
  have hs := (periodic_s a b t).image_Icc (by positivity : 0 < 2 * π) 0
  have ht := (periodic_t a b s).image_Icc (by positivity : 0 < 2 * π) 0
  simp only [zero_add] at hs ht
  obtain ⟨s', hs', he⟩ := hs.symm ▸ (mem_range_self s)
  have ht' := (periodic_t a b s').image_Icc (by positivity : 0 < 2 * π) 0
  simp only [zero_add] at ht'
  obtain ⟨t', ht'', he'⟩ := ht'.symm ▸ (mem_range_self t)
  exact ⟨(s',t'), ⟨hs',ht''⟩, he'.trans he⟩

theorem compact_surface {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsCompact (surface a b) := by
  rw [← range_eq_surface ha hab, ← fundamental_square]
  exact (isCompact_Icc.prod isCompact_Icc).image (continuous_torus a b)

/-- Equality of fibers recovers both pairs of sine and cosine values. -/
theorem fiber_trig {a b s t u v : ℝ} (ha : 0 < a) (hab : a < b) :
    torus a b s t = torus a b u v ↔
      cos s = cos u ∧ sin s = sin u ∧ cos t = cos v ∧ sin t = sin v := by
  constructor
  · intro h
    have h0 := congrArg (fun p : E3 => p 0) h
    have h1 := congrArg (fun p : E3 => p 1) h
    have h2 := congrArg (fun p : E3 => p 2) h
    have hr : (b + a * cos s) ^ 2 = (b + a * cos u) ^ 2 := by
      rw [← radial_identity a b s t, ← radial_identity a b u v, h]
    have hrs := radius_pos ha hab s
    have hru := radius_pos ha hab u
    have hr' : b + a * cos s = b + a * cos u :=
      (sq_eq_sq₀ hrs.le hru.le).mp hr
    have hc : cos s = cos u := by nlinarith
    dsimp [torus, point] at h0 h1 h2
    rw [hc] at h0 h1
    exact ⟨hc, mul_left_cancel₀ ha.ne' h2,
      mul_left_cancel₀ hru.ne' h0, mul_left_cancel₀ hru.ne' h1⟩
  · rintro ⟨hc,hs,hc',hs'⟩; simp [torus,hc,hs,hc',hs']

def velocity (a b l t : ℝ) : E3 :=
  point (-a * sin t * cos (l*t) - l * (b+a*cos t) * sin (l*t))
    (-a * sin t * sin (l*t) + l * (b+a*cos t) * cos (l*t)) (a*cos t)

theorem winding_hasDerivAt (a b l t : ℝ) :
    HasDerivAt (winding a b l) (velocity a b l t) t := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [winding, torus, velocity, point]
  · convert (((hasDerivAt_cos t).const_mul a).const_add b).mul
      ((hasDerivAt_cos (l*t)).comp t ((hasDerivAt_id t).const_mul l)) using 1 <;>
      first | rfl | dsimp; ring
  · convert (((hasDerivAt_cos t).const_mul a).const_add b).mul
      ((hasDerivAt_sin (l*t)).comp t ((hasDerivAt_id t).const_mul l)) using 1 <;>
      first | rfl | dsimp; ring
  · exact (hasDerivAt_sin t).const_mul a

/-- The norm here is the Euclidean norm, not the coordinate supremum norm. -/
theorem speed (a b l t : ℝ) :
    ‖deriv (winding a b l) t‖ ^ 2 = a ^ 2 + l ^ 2 * (b + a * cos t) ^ 2 := by
  rw [(winding_hasDerivAt a b l t).deriv, EuclideanSpace.norm_sq_eq]
  simp [velocity, point, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  nlinarith [sin_sq_add_cos_sq t, sin_sq_add_cos_sq (l*t),
    mul_nonneg (sq_nonneg a) (sq_nonneg (sin t))]

def parameters (s t : ℝ) : E2 := WithLp.toLp 2 ![s,t]
def parametrization (a b : ℝ) (u : E2) : E3 := torus a b (u 0) (u 1)
def first (a b : ℝ) (u : E2) : ℝ := parametrization a b u 0
def third (a b : ℝ) (u : E2) : ℝ := parametrization a b u 2

def firstGradient (a b : ℝ) (u : E2) : E2 :=
  parameters (-a * sin (u 0) * cos (u 1)) (-(b+a*cos (u 0))*sin (u 1))
def thirdGradient (a : ℝ) (u : E2) : E2 := parameters (a*cos (u 0)) 0

theorem first_hasGradientAt (a b : ℝ) (u : E2) :
    HasGradientAt (first a b) (firstGradient a b u) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (((PiLp.hasFDerivAt_apply 2 u 0).cos.const_mul a).const_add b).mul
    (PiLp.hasFDerivAt_apply 2 u 1).cos
  convert h using 1
  · rfl
  · ext v
    simp [firstGradient, parameters, InnerProductSpace.toDual_apply_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
    ring

theorem third_hasGradientAt (a b : ℝ) (u : E2) :
    HasGradientAt (third a b) (thirdGradient a u) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((PiLp.hasFDerivAt_apply 2 u 0).sin.const_mul a) using 1
  · rfl
  · ext v
    simp [thirdGradient, parameters, InnerProductSpace.toDual_apply_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
    ring

theorem first_gradient_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : E2) :
    gradient (first a b) u = 0 ↔ sin (u 0) = 0 ∧ sin (u 1) = 0 := by
  rw [(first_hasGradientAt a b u).gradient]
  constructor
  · intro h
    have h0 := congrArg (fun v : E2 => v 0) h
    have h1 := congrArg (fun v : E2 => v 1) h
    simp only [firstGradient, parameters, PiLp.zero_apply] at h0 h1
    have ht : sin (u 1) = 0 := (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr
      (radius_pos ha hab (u 0)).ne')
    have hc : cos (u 1) ≠ 0 := by
      have := sin_sq_add_cos_sq (u 1); rw [ht] at this; nlinarith
    exact ⟨(mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hc)).resolve_left
      (neg_ne_zero.mpr ha.ne'), ht⟩
  · rintro ⟨hs,ht⟩
    ext i; fin_cases i <;> simp [firstGradient, parameters, hs, ht]

theorem third_gradient_zero {a b : ℝ} (ha : 0 < a) (u : E2) :
    gradient (third a b) u = 0 ↔ cos (u 0) = 0 := by
  rw [(third_hasGradientAt a b u).gradient]
  constructor
  · intro h
    have := congrArg (fun v : E2 => v 0) h
    simpa [thirdGradient, parameters, ha.ne'] using this
  · intro h; ext i; fin_cases i <;> simp [thirdGradient, parameters, h]

/-- The universal quantifier is over the entire fiber, not one selected inverse. -/
def criticalFiber (a b : ℝ) (i : Fin 3) (p : E3) : Prop :=
  p ∈ surface a b ∧ ∀ u : E2, parametrization a b u = p →
    gradient (fun v => parametrization a b v i) u = 0

def firstCriticalPoints (a b : ℝ) : Finset E3 :=
  {point (b+a) 0 0, point (-(b+a)) 0 0, point (b-a) 0 0, point (-(b-a)) 0 0}

theorem first_gradient_image {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : E2) :
    gradient (first a b) u = 0 ↔ parametrization a b u ∈ firstCriticalPoints a b := by
  rw [first_gradient_zero ha hab]
  constructor
  · rintro ⟨hs,ht⟩
    rcases sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
      rcases sin_eq_zero_iff_cos_eq.mp ht with hd | hd <;>
      simp [parametrization, torus, hs, ht, hc, hd, firstCriticalPoints, sub_eq_add_neg]
  · intro hp
    have hz : parametrization a b u 2 = 0 ∧ parametrization a b u 1 = 0 := by
      simp only [firstCriticalPoints, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h <;> rw [h] <;> simp
    dsimp [parametrization, torus, point] at hz
    exact ⟨(mul_eq_zero.mp hz.1).resolve_left ha.ne',
      (mul_eq_zero.mp hz.2).resolve_left (radius_pos ha hab _).ne'⟩

theorem firstCriticalPoints_subset {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (firstCriticalPoints a b : Set E3) ⊆ surface a b := by
  intro p hp
  simp only [firstCriticalPoints, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp
  have h00 := torus_mem_surface ha hab 0 0
  have h0p := torus_mem_surface ha hab 0 π
  have hp0 := torus_mem_surface ha hab π 0
  have hpp := torus_mem_surface ha hab π π
  rcases hp with rfl | rfl | rfl | rfl
  · simpa [torus] using h00
  · simpa [torus] using h0p
  · simpa [torus, sub_eq_add_neg] using hp0
  · simpa [torus, sub_eq_add_neg] using hpp

/-- Part (a): these four points, and no others, have a zero gradient on their fiber. -/
theorem first_critical {a b : ℝ} (ha : 0 < a) (hab : a < b) (p : E3) :
    criticalFiber a b 0 p ↔ p ∈ firstCriticalPoints a b := by
  constructor
  · rintro ⟨hp,h⟩
    obtain ⟨⟨s,t⟩,he⟩ := (range_eq_surface ha hab).symm ▸ hp
    have hg := h (parameters s t) he
    exact he ▸ (first_gradient_image ha hab (parameters s t)).mp hg
  · intro hp
    refine ⟨firstCriticalPoints_subset ha hab hp, ?_⟩
    intro u hu
    exact (first_gradient_image ha hab u).mpr (hu ▸ hp)

theorem four_distinct {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (firstCriticalPoints a b).card = 4 := by
  have nepoint : ∀ {x y : ℝ}, x ≠ y → point x 0 0 ≠ point y 0 0 := by
    intro x y h he; exact h (congrArg (fun p : E3 => p 0) he)
  have h1 : point (b+a) 0 0 ≠ point (-(b+a)) 0 0 := nepoint (by linarith)
  have h2 : point (b+a) 0 0 ≠ point (b-a) 0 0 := nepoint (by linarith)
  have h3 : point (b+a) 0 0 ≠ point (-(b-a)) 0 0 := nepoint (by linarith)
  have h4 : point (-(b+a)) 0 0 ≠ point (b-a) 0 0 := nepoint (by linarith)
  have h5 : point (-(b+a)) 0 0 ≠ point (-(b-a)) 0 0 := nepoint (by linarith)
  have h6 : point (b-a) 0 0 ≠ point (-(b-a)) 0 0 := nepoint (by linarith)
  simp only [firstCriticalPoints, Finset.card_insert_of_notMem, Finset.mem_insert,
    Finset.mem_singleton, h1,h2,h3,h4,h5,h6, false_or, not_false_eq_true,
    Finset.card_singleton]

/-- Part (b): the upper and lower horizontal circles on the torus. -/
theorem third_critical {a b : ℝ} (ha : 0 < a) (hab : a < b) (p : E3) :
    criticalFiber a b 2 p ↔ p ∈ surface a b ∧ (p 2 = a ∨ p 2 = -a) := by
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp, ?_⟩
    obtain ⟨⟨s,t⟩,he⟩ := (range_eq_surface ha hab).symm ▸ hp
    have hg := (third_gradient_zero ha (parameters s t)).mp (h (parameters s t) he)
    change cos s = 0 at hg
    rcases cos_eq_zero_iff_sin_eq.mp hg with hs | hs <;>
      simp [← he, torus, point, hs]
  · rintro ⟨hp,hz⟩
    refine ⟨hp, ?_⟩
    intro u hu
    apply (third_gradient_zero ha u).mpr
    have h : a * sin (u 0) = a ∨ a * sin (u 0) = -a := by
      simpa [← hu, parametrization, torus, point] using hz
    apply cos_eq_zero_iff_sin_eq.mpr
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith

/-- Equality of both trigonometric coordinates means equality modulo a full turn. -/
theorem trig_eq_iff (x y : ℝ) :
    cos x = cos y ∧ sin x = sin y ↔ ∃ k : ℤ, y = x + k * (2*π) := by
  constructor
  · rintro ⟨hc,hs⟩
    have h : ((y-x : ℝ) : Real.Angle) = 0 := by
      rw [Real.Angle.coe_sub, Real.Angle.cos_sin_inj hc hs, sub_self]
    obtain ⟨k,hk⟩ := Real.Angle.coe_eq_zero_iff.mp h
    exact ⟨k, by simpa only [zsmul_eq_mul] using (eq_add_of_sub_eq hk.symm).trans (add_comm _ _)⟩
  · rintro ⟨k,rfl⟩
    exact ⟨((cos_periodic.int_mul k) x).symm, ((sin_periodic.int_mul k) x).symm⟩

/-- Full fibers: the only identifications are independent full turns in the parameters. -/
theorem fibers {a b s t u v : ℝ} (ha : 0 < a) (hab : a < b) :
    torus a b s t = torus a b u v ↔
      (∃ k : ℤ, u = s + k*(2*π)) ∧ (∃ m : ℤ, v = t + m*(2*π)) := by
  rw [fiber_trig ha hab]
  simp only [← trig_eq_iff, and_assoc]

/-- Part (d): irrational winding never repeats a point. -/
theorem winding_injective {a b l : ℝ} (ha : 0 < a) (hab : a < b)
    (hl : Irrational l) : Function.Injective (winding a b l) := by
  intro x y h
  obtain ⟨⟨k,hk⟩,⟨m,hm⟩⟩ := (fibers ha hab).mp h
  have he : l * (k : ℝ) = (m : ℝ) := by
    have hp := Real.pi_pos
    nlinarith [show l*y = l*x + l*k*(2*π) by rw [hk]; ring]
  have hk0 : k = 0 := by
    by_contra hk0
    exact hl.ne_rational m k ((eq_div_iff (Int.cast_ne_zero.mpr hk0)).mpr he)
  simpa [hk0] using hk.symm

/-- Part (d): the closure is exactly K. The density input is Mathlib's
irrational-rotation theorem for a circle of circumference `2π`. -/
theorem winding_closure {a b l : ℝ} (ha : 0 < a) (hab : a < b)
    (hl : Irrational l) : closure (Set.range (winding a b l)) = surface a b := by
  apply Subset.antisymm
  · apply closure_minimal _ (compact_surface ha hab).isClosed
    rintro p ⟨t,rfl⟩; exact torus_mem_surface ha hab t (l*t)
  · intro p hp
    obtain ⟨⟨s,t⟩,rfl⟩ := (range_eq_surface ha hab).symm ▸ hp
    let F : Real.Angle → E3 := fun θ =>
      point ((b+a*cos s)*(θ + (l*s : ℝ)).cos)
        ((b+a*cos s)*(θ + (l*s : ℝ)).sin) (a*sin s)
    have hF : Continuous F := by
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i; fin_cases i <;> dsimp [F, point]
      · exact continuous_const.mul (Real.Angle.continuous_cos.comp
          (continuous_id.add continuous_const))
      · exact continuous_const.mul (Real.Angle.continuous_sin.comp
          (continuous_id.add continuous_const))
      · exact continuous_const
    have hd : DenseRange (fun n : ℤ => n • ((l*(2*π) : ℝ) : Real.Angle)) :=
      AddCircle.denseRange_zsmul_coe_iff.mpr (by
        simpa [mul_div_cancel_right₀ _ (by positivity : 2*π ≠ 0)] using hl)
    have hmem : torus a b s t ∈ Set.range F := by
      refine ⟨((t-l*s : ℝ) : Real.Angle), ?_⟩
      simp [F, torus]
    apply closure_mono (s := F '' Set.range (fun n : ℤ =>
      n • ((l*(2*π) : ℝ) : Real.Angle))) ?_
      (hF.range_subset_closure_image_dense hd hmem)
    rintro q ⟨θ,⟨n,rfl⟩,rfl⟩
    refine ⟨s+n*(2*π), ?_⟩
    have he : n • ((l*(2*π) : ℝ) : Real.Angle) + ((l*s : ℝ) : Real.Angle) =
        ((l*(s+n*(2*π)) : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_zsmul, ← Real.Angle.coe_add]
      congr 1
      simp only [zsmul_eq_mul]; ring
    dsimp [winding]
    apply (((periodic_s a b (l*(s+n*(2*π)))).int_mul n) s).trans
    simp only [F, he, Real.Angle.cos_coe, Real.Angle.sin_coe, torus]

/-- A saddle takes strictly smaller and strictly larger values in every neighborhood. -/
def Saddle (f : E2 → ℝ) (u : E2) : Prop :=
  ∀ U ∈ 𝓝 u, (∃ v ∈ U, f v < f u) ∧ (∃ v ∈ U, f u < f v)

theorem Saddle.neither {f : E2 → ℝ} {u : E2} (h : Saddle f u) :
    ¬ IsLocalMin f u ∧ ¬ IsLocalMax f u := by
  constructor
  · intro hm
    obtain ⟨v,hv,hlt⟩ := (h {v | f u ≤ f v} hm).1
    exact (not_lt_of_ge hv) hlt
  · intro hm
    obtain ⟨v,hv,hlt⟩ := (h {v | f v ≤ f u} hm).2
    exact (not_lt_of_ge hv) hlt

theorem first_bounds {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : E2) :
    -(b+a) ≤ first a b u ∧ first a b u ≤ b+a := by
  have hr := radius_pos ha hab (u 0)
  have hhi := mul_le_mul_of_nonneg_left (cos_le_one (u 1)) hr.le
  have hlo := mul_le_mul_of_nonneg_left (neg_one_le_cos (u 1)) hr.le
  dsimp [first, parametrization, torus, point]
  constructor <;> nlinarith [cos_le_one (u 0)]

theorem third_bounds {a b : ℝ} (ha : 0 < a) (u : E2) :
    -a ≤ third a b u ∧ third a b u ≤ a := by
  dsimp [third, parametrization, torus, point]
  constructor <;> nlinarith [neg_one_le_sin (u 0), sin_le_one (u 0)]

/-- Part (c): the outer positive point gives a global, hence local, maximum
at every parameter in its fiber. -/
theorem first_maximum {a b : ℝ} (ha : 0 < a) (hab : a < b) {u : E2}
    (hu : parametrization a b u = point (b+a) 0 0) :
    (∀ v, first a b v ≤ first a b u) ∧ IsLocalMax (first a b) u := by
  have he : first a b u = b+a := congrArg (fun p : E3 => p 0) hu
  have h : ∀ v, first a b v ≤ first a b u := fun v => he ▸ (first_bounds ha hab v).2
  exact ⟨h, Filter.Eventually.of_forall h⟩

/-- The outer negative point gives a global, hence local, minimum. -/
theorem first_minimum {a b : ℝ} (ha : 0 < a) (hab : a < b) {u : E2}
    (hu : parametrization a b u = point (-(b+a)) 0 0) :
    (∀ v, first a b u ≤ first a b v) ∧ IsLocalMin (first a b) u := by
  have he : first a b u = -(b+a) := congrArg (fun p : E3 => p 0) hu
  have h : ∀ v, first a b u ≤ first a b v := fun v => he ▸ (first_bounds ha hab v).1
  exact ⟨h, Filter.Eventually.of_forall h⟩

/-- The upper circle gives global maxima of the third coordinate. -/
theorem third_maximum {a b : ℝ} (ha : 0 < a) {u : E2}
    (hu : parametrization a b u 2 = a) :
    (∀ v, third a b v ≤ third a b u) ∧ IsLocalMax (third a b) u := by
  have h : ∀ v, third a b v ≤ third a b u := by
    intro v
    change third a b u = a at hu
    rw [hu]
    exact (third_bounds ha v).2
  exact ⟨h, Filter.Eventually.of_forall h⟩

/-- The lower circle gives global minima of the third coordinate. -/
theorem third_minimum {a b : ℝ} (ha : 0 < a) {u : E2}
    (hu : parametrization a b u 2 = -a) :
    (∀ v, third a b u ≤ third a b v) ∧ IsLocalMin (third a b) u := by
  have h : ∀ v, third a b u ≤ third a b v := by
    intro v
    change third a b u = -a at hu
    rw [hu]
    exact (third_bounds ha v).1
  exact ⟨h, Filter.Eventually.of_forall h⟩

theorem small_positive {P : ℝ → Prop} (hP : ∀ᶠ h in 𝓝 (0 : ℝ), P h) :
    ∃ h, 0 < h ∧ h < π ∧ P h := by
  obtain ⟨δ,hδ,hP⟩ := Metric.eventually_nhds_iff.mp hP
  obtain ⟨h,hh0,hh⟩ := exists_between (lt_min hδ pi_pos)
  refine ⟨h,hh0,(lt_min_iff.mp hh).2,hP ?_⟩
  simpa [Real.dist_eq, abs_of_pos hh0] using (lt_min_iff.mp hh).1

theorem parameters_eta (u : E2) : parameters (u 0) (u 1) = u := by
  ext i; fin_cases i <;> rfl

theorem first_saddle_trig {a b : ℝ} (ha : 0 < a) (hab : a < b) {u : E2}
    (hs : sin (u 0) = 0) (hc : cos (u 0) = -1) (ht : sin (u 1) = 0) :
    Saddle (first a b) u := by
  intro U hU
  let S : ℝ → E2 := fun h => parameters (u 0+h) (u 1)
  let T : ℝ → E2 := fun h => parameters (u 0) (u 1+h)
  have hS : Continuous S := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i; fin_cases i <;> dsimp [S, parameters] <;> fun_prop
  have hT : Continuous T := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i; fin_cases i <;> dsimp [T, parameters] <;> fun_prop
  have hS0 : S 0 = u := by simpa [S] using parameters_eta u
  have hT0 : T 0 = u := by simpa [T] using parameters_eta u
  have hSU : ∀ᶠ h in 𝓝 (0 : ℝ), S h ∈ U :=
    (hS.continuousAt.tendsto.mono_right (le_of_eq (congrArg nhds hS0))) hU
  have hTU : ∀ᶠ h in 𝓝 (0 : ℝ), T h ∈ U :=
    (hT.continuousAt.tendsto.mono_right (le_of_eq (congrArg nhds hT0))) hU
  have hnear : ∀ᶠ h in 𝓝 (0 : ℝ), S h ∈ U ∧ T h ∈ U := hSU.and hTU
  obtain ⟨h,hh0,hhπ,hSU,hTU⟩ := small_positive hnear
  have hcos : cos h < 1 := by
    simpa using strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨hh0.le,hhπ.le⟩ hh0
  have hSv : first a b (S h) = (b-a*cos h)*cos (u 1) := by
    simp [first, parametrization, torus, point, S, parameters, cos_add, hs, hc, sub_eq_add_neg]
  have hTv : first a b (T h) = (b-a)*cos (u 1)*cos h := by
    simp [first, parametrization, torus, point, T, parameters, cos_add, ht, hc,
      sub_eq_add_neg, mul_assoc]
  have hu : first a b u = (b-a)*cos (u 1) := by
    simp [first, parametrization, torus, point, hc, sub_eq_add_neg]
  rcases sin_eq_zero_iff_cos_eq.mp ht with hd | hd
  · refine ⟨⟨T h,hTU,?_⟩,⟨S h,hSU,?_⟩⟩ <;> rw [hu, hd]
    · rw [hTv,hd]; nlinarith
    · rw [hSv,hd]; nlinarith
  · refine ⟨⟨S h,hSU,?_⟩,⟨T h,hTU,?_⟩⟩ <;> rw [hu, hd]
    · rw [hSv,hd]; nlinarith
    · rw [hTv,hd]; nlinarith

/-- Both inner equatorial points are saddles at every point of their fibers. -/
theorem first_saddles {a b : ℝ} (ha : 0 < a) (hab : a < b) {u : E2}
    (hu : parametrization a b u = point (b-a) 0 0 ∨
      parametrization a b u = point (-(b-a)) 0 0) :
    Saddle (first a b) u ∧ ¬ IsLocalMin (first a b) u ∧ ¬ IsLocalMax (first a b) u := by
  have he0 : torus a b π 0 = point (b-a) 0 0 := by simp [torus, sub_eq_add_neg]
  have heπ : torus a b π π = point (-(b-a)) 0 0 := by simp [torus, sub_eq_add_neg]
  have hh : sin (u 0) = 0 ∧ cos (u 0) = -1 ∧ sin (u 1) = 0 := by
    rcases hu with hu | hu
    · have ht := (fiber_trig ha hab).mp (hu.trans he0.symm)
      simp only [sin_pi, cos_pi, sin_zero, cos_zero] at ht
      exact ⟨ht.2.1,ht.1,ht.2.2.2⟩
    · have ht := (fiber_trig ha hab).mp (hu.trans heπ.symm)
      simp only [sin_pi, cos_pi] at ht
      exact ⟨ht.2.1,ht.1,ht.2.2.2⟩
  have h := first_saddle_trig ha hab hh.1 hh.2.1 hh.2.2
  exact ⟨h,h.neither⟩

/-- An explicit cardinality statement for the set in (a). -/
theorem first_critical_count {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    {p | criticalFiber a b 0 p}.ncard = 4 := by
  have he : {p | criticalFiber a b 0 p} = (firstCriticalPoints a b : Set E3) := by
    ext p; exact first_critical ha hab p
  rw [he, Set.ncard_coe_finset, four_distinct ha hab]

/-- The set in (b) consists of precisely the circles of radius b at heights ±a. -/
theorem third_critical_circles {a b : ℝ} (ha : 0 < a) (hab : a < b) (p : E3) :
    criticalFiber a b 2 p ↔ p 0 ^ 2 + p 1 ^ 2 = b ^ 2 ∧ (p 2 = a ∨ p 2 = -a) := by
  rw [third_critical ha hab]
  constructor
  · rintro ⟨hp,hz⟩
    refine ⟨?_,hz⟩
    have hr := Real.sq_sqrt (show 0 ≤ p 0 ^ 2 + p 1 ^ 2 by positivity)
    change (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)-b)^2 + p 2 ^ 2 = a^2 at hp
    have he : (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)-b)^2 = 0 := by
      rcases hz with hz | hz <;> rw [hz] at hp <;> nlinarith
    have he' := sub_eq_zero.mp (sq_eq_zero_iff.mp he)
    rw [he'] at hr
    exact hr.symm
  · rintro ⟨hr,hz⟩
    refine ⟨?_,hz⟩
    change (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)-b)^2 + p 2 ^ 2 = a^2
    rw [hr, Real.sqrt_sq (by linarith : 0 ≤ b)]
    rcases hz with hz | hz <;> simp [hz]

theorem continuous_parametrization (a b : ℝ) : Continuous (parametrization a b) := by
  have h : Continuous (fun u : E2 => (u 0, u 1)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  change Continuous ((fun z : ℝ × ℝ => torus a b z.1 z.2) ∘
    (fun u : E2 => (u 0, u 1)))
  exact Continuous.comp (continuous_torus a b) h

/-- The saddle interpretation also holds in the relative topology of the actual
surface: every ambient neighborhood contains surface points on both sides. -/
theorem first_surface_saddles {a b : ℝ} (ha : 0 < a) (hab : a < b) {p : E3}
    (hp : p = point (b-a) 0 0 ∨ p = point (-(b-a)) 0 0) :
    p ∈ surface a b ∧ ∀ U ∈ 𝓝 p,
      (∃ q ∈ U ∩ surface a b, q 0 < p 0) ∧
      (∃ q ∈ U ∩ surface a b, p 0 < q 0) := by
  have hpK : p ∈ surface a b := firstCriticalPoints_subset ha hab (by
    simp only [firstCriticalPoints, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rcases hp with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h)))
  refine ⟨hpK, ?_⟩
  obtain ⟨⟨s,t⟩,he⟩ := (range_eq_surface ha hab).symm ▸ hpK
  let u := parameters s t
  have hu : parametrization a b u = p := he
  have hs := (first_saddles ha hab (hu ▸ hp)).1
  intro U hU
  have hpre : parametrization a b ⁻¹' U ∈ 𝓝 u :=
    ((continuous_parametrization a b).continuousAt.tendsto.mono_right
      (le_of_eq (congrArg nhds hu))) hU
  obtain ⟨⟨v,hv,hv'⟩,⟨w,hw,hw'⟩⟩ := hs _ hpre
  refine ⟨⟨parametrization a b v, ⟨hv,torus_mem_surface ha hab _ _⟩, ?_⟩,
    ⟨parametrization a b w, ⟨hw,torus_mem_surface ha hab _ _⟩, ?_⟩⟩
  · change first a b v < _
    simpa only [first, hu] using hv'
  · change _ < first a b w
    simpa only [first, hu] using hw'

/-- A nonzero cosine profile excludes the opposite local extremum. -/
theorem cosine_profile {f : E2 → ℝ} {u : E2} {P : ℝ → E2}
    (hP : Continuous P) (hP0 : P 0 = u) (hf : ∀ h, f (P h) = f u * cos h) :
    (0 < f u → ¬ IsLocalMin f u) ∧ (f u < 0 → ¬ IsLocalMax f u) := by
  have hc : ∀ h : ℝ, 0 < h → h < π → cos h < 1 := by
    intro h hh hhπ
    simpa using strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨hh.le,hhπ.le⟩ hh
  constructor
  · intro hpos hmin
    have hn : ∀ᶠ h in 𝓝 (0 : ℝ), f u ≤ f (P h) :=
      (hP.continuousAt.tendsto.mono_right (le_of_eq (congrArg nhds hP0))) hmin
    obtain ⟨h,hh,hhπ,hle⟩ := small_positive hn
    rw [hf] at hle
    nlinarith [hc h hh hhπ]
  · intro hneg hmax
    have hn : ∀ᶠ h in 𝓝 (0 : ℝ), f (P h) ≤ f u :=
      (hP.continuousAt.tendsto.mono_right (le_of_eq (congrArg nhds hP0))) hmax
    obtain ⟨h,hh,hhπ,hle⟩ := small_positive hn
    rw [hf] at hle
    nlinarith [hc h hh hhπ]

theorem first_opposite_extremum (a b : ℝ) (u : E2) (ht : sin (u 1) = 0) :
    (0 < first a b u → ¬ IsLocalMin (first a b) u) ∧
    (first a b u < 0 → ¬ IsLocalMax (first a b) u) := by
  apply cosine_profile (P := fun h => parameters (u 0) (u 1+h))
  · apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i; fin_cases i <;> dsimp [parameters] <;> fun_prop
  · simpa using parameters_eta u
  · intro h
    simp [first, parametrization, torus, point, parameters, cos_add, ht, mul_assoc]

theorem third_opposite_extremum (a b : ℝ) (u : E2) (hs : cos (u 0) = 0) :
    (0 < third a b u → ¬ IsLocalMin (third a b) u) ∧
    (third a b u < 0 → ¬ IsLocalMax (third a b) u) := by
  apply cosine_profile (P := fun h => parameters (u 0+h) (u 1))
  · apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i; fin_cases i <;> dsimp [parameters] <;> fun_prop
  · simpa using parameters_eta u
  · intro h
    simp [third, parametrization, torus, point, parameters, sin_add, hs, mul_assoc]

/-- Complete local maximum classification for the first coordinate, on all of R². -/
theorem first_local_max_iff {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : E2) :
    IsLocalMax (first a b) u ↔ parametrization a b u = point (b+a) 0 0 := by
  constructor
  · intro h
    have hg : gradient (first a b) u = 0 := by
      apply (InnerProductSpace.toDual ℝ E2).injective
      rw [toDual_gradient, h.fderiv_eq_zero, map_zero]
    have ht := (first_gradient_zero ha hab u).mp hg
    have hi := (first_gradient_image ha hab u).mp hg
    simp only [firstCriticalPoints, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi | hi
    · exact hi
    · have he : first a b u = -(b+a) := congrArg (fun p : E3 => p 0) hi
      exact False.elim ((first_opposite_extremum a b u ht.2).2 (by rw [he]; linarith) h)
    · exact False.elim ((first_saddles ha hab (Or.inl hi)).2.2 h)
    · exact False.elim ((first_saddles ha hab (Or.inr hi)).2.2 h)
  · intro h; exact (first_maximum ha hab h).2

/-- Complete local minimum classification for the first coordinate. -/
theorem first_local_min_iff {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : E2) :
    IsLocalMin (first a b) u ↔ parametrization a b u = point (-(b+a)) 0 0 := by
  constructor
  · intro h
    have hg : gradient (first a b) u = 0 := by
      apply (InnerProductSpace.toDual ℝ E2).injective
      rw [toDual_gradient, h.fderiv_eq_zero, map_zero]
    have ht := (first_gradient_zero ha hab u).mp hg
    have hi := (first_gradient_image ha hab u).mp hg
    simp only [firstCriticalPoints, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi | hi
    · have he : first a b u = b+a := congrArg (fun p : E3 => p 0) hi
      exact False.elim ((first_opposite_extremum a b u ht.2).1 (by rw [he]; linarith) h)
    · exact hi
    · exact False.elim ((first_saddles ha hab (Or.inl hi)).2.1 h)
    · exact False.elim ((first_saddles ha hab (Or.inr hi)).2.1 h)
  · intro h; exact (first_minimum ha hab h).2

/-- The third coordinate has local maxima precisely on the upper circle. -/
theorem third_local_max_iff {a b : ℝ} (ha : 0 < a) (u : E2) :
    IsLocalMax (third a b) u ↔ parametrization a b u 2 = a := by
  constructor
  · intro h
    have hg : gradient (third a b) u = 0 := by
      apply (InnerProductSpace.toDual ℝ E2).injective
      rw [toDual_gradient, h.fderiv_eq_zero, map_zero]
    have hs := (third_gradient_zero ha u).mp hg
    rcases cos_eq_zero_iff_sin_eq.mp hs with hz | hz
    · simp [parametrization, torus, point, hz]
    · have he : third a b u = -a := by simp [third, parametrization, torus, point, hz]
      exact False.elim ((third_opposite_extremum a b u hs).2 (by rw [he]; linarith) h)
  · intro h; exact (third_maximum ha h).2

/-- The third coordinate has local minima precisely on the lower circle. -/
theorem third_local_min_iff {a b : ℝ} (ha : 0 < a) (u : E2) :
    IsLocalMin (third a b) u ↔ parametrization a b u 2 = -a := by
  constructor
  · intro h
    have hg : gradient (third a b) u = 0 := by
      apply (InnerProductSpace.toDual ℝ E2).injective
      rw [toDual_gradient, h.fderiv_eq_zero, map_zero]
    have hs := (third_gradient_zero ha u).mp hg
    rcases cos_eq_zero_iff_sin_eq.mp hs with hz | hz
    · have he : third a b u = a := by simp [third, parametrization, torus, point, hz]
      exact False.elim ((third_opposite_extremum a b u hs).1 (by rw [he]; linarith) h)
    · simp [parametrization, torus, point, hz]
  · intro h; exact (third_minimum ha h).2

end Rudin.Chapter09.Exercise12
