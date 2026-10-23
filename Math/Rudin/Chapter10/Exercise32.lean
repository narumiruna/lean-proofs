module
public import Math.Rudin.Support.SmoothChains
public import Math.Rudin.Chapter10.Exercise21
public import Mathlib.Tactic

/-! # Chapter 10, Exercise 32

The band is the image of the actual source rectangle under Rudin's map.
Full path maps retain orientation and the twice-traversed seam. Nonorientability
means that the image has no continuous nowhere-zero Euclidean normal field;
its proof uses actual tangent derivatives and the intermediate value theorem.
The free rim has a proved complete closed parameterization. Analytic Stokes
computes the parameter boundary integral, separately from the rim integral.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise32
open Set
open Rudin.Support
open OrientedChains.Parametric

abbrev Space := ℝ × ℝ × ℝ
/-- The closed source rectangle specified in the exercise. -/
def source (δ : ℝ) : Set (ℝ × ℝ) := Icc 0 Real.pi ×ˢ Icc (-δ) δ
/-- The actual full nonlinear map from the source rectangle. -/
abbrev phi : (ℝ × ℝ) → Space := mobius
/-- The band is the image of the rectangle, not a formal integration functional. -/
def band (δ : ℝ) : Set Space := phi '' source δ

def a (δ : ℝ) : Space := (1, 0, -δ)
def b (δ : ℝ) : Space := (1, 0, δ)
def p1 (δ : ℝ) : ℝ × ℝ := (0, -δ)
def p2 (δ : ℝ) : ℝ × ℝ := (Real.pi, -δ)
def p3 (δ : ℝ) : ℝ × ℝ := (Real.pi, δ)
def p4 (δ : ℝ) : ℝ × ℝ := (0, δ)

def edge1 (δ : ℝ) : ℝ → Space := phi ∘ segment (p1 δ) (p2 δ)
def edge2 (δ : ℝ) : ℝ → Space := phi ∘ segment (p2 δ) (p3 δ)
def edge3 (δ : ℝ) : ℝ → Space := phi ∘ segment (p3 δ) (p4 δ)
def edge4 (δ : ℝ) : ℝ → Space := phi ∘ segment (p4 δ) (p1 δ)

theorem seam (t : ℝ) : phi (Real.pi, t) = phi (0, -t) := mobius_seam t

theorem corner_images (δ : ℝ) :
    phi (p1 δ) = a δ ∧ phi (p3 δ) = a δ ∧
    phi (p2 δ) = b δ ∧ phi (p4 δ) = b δ := by
  norm_num [phi, mobius, p1, p2, p3, p4, a, b, Real.sin_two_mul, Real.cos_two_mul]

theorem edge1_full (δ : ℝ) : edge1 δ = fun t => mobiusSquare δ (t, 0) := by
  funext t
  apply congrArg phi
  ext <;> simp [OrientedChains.Parametric.segment, p1, p2]
  <;> ring

theorem edge2_full (δ : ℝ) : edge2 δ = fun t => mobiusSquare δ (1, t) := by
  funext t
  apply congrArg phi
  ext <;> simp [OrientedChains.Parametric.segment, p2, p3]
  <;> ring

theorem edge3_full (δ : ℝ) : edge3 δ = reverse (fun t => mobiusSquare δ (t, 1)) := by
  funext t
  apply congrArg phi
  ext <;> simp [OrientedChains.Parametric.segment, p3, p4]
  <;> ring

theorem edge4_full (δ : ℝ) : edge4 δ = reverse (fun t => mobiusSquare δ (0, t)) := by
  funext t
  apply congrArg phi
  ext <;> simp [OrientedChains.Parametric.segment, p4, p1]
  ring

/-- The four restrictions are full oriented maps, not segments joining image corners. -/
theorem boundary_decomposition (δ : ℝ) :
    surfaceBoundary (surface (mobiusSquare δ)) =
      path (edge1 δ) + path (edge2 δ) + path (edge3 δ) + path (edge4 δ) := by
  rw [edge1_full, edge2_full, edge3_full, edge4_full, path_reverse, path_reverse,
    surfaceBoundary_surface]
  abel

theorem repeated_seam_maps (δ : ℝ) : edge2 δ = segment (b δ) (a δ) ∧
    edge4 δ = segment (b δ) (a δ) := by
  constructor <;> funext t <;>
    ext <;> norm_num [edge2, edge4, Function.comp_def, phi, mobius, OrientedChains.Parametric.segment,
      p2, p3, p4, p1, a, b, ← add_mul, Real.sin_two_mul, Real.cos_two_mul]
  ring

/-- The repeated seam has integer coefficient two in the signed full-map chain. -/
theorem boundary_repeated_seam (δ : ℝ) :
    surfaceBoundary (surface (mobiusSquare δ)) =
      path (edge1 δ) + path (edge3 δ) + (2 : ℤ) • path (edge2 δ) := by
  rw [boundary_decomposition, (repeated_seam_maps δ).2, ← (repeated_seam_maps δ).1]
  abel

theorem triangulated_boundary (δ : ℝ) :
    SmoothChains.toPaths (SmoothChains.boundary 1
      (SmoothChains.triangulate (mobiusSquare δ) (SmoothChains.mobiusSquare_smooth δ))) =
      path (edge1 δ) + path (edge3 δ) + (2 : ℤ) • path (edge2 δ) := by
  rw [SmoothChains.triangulate_boundary, boundary_repeated_seam]

/-- The source's single closed edge parameterization, on `[0,2π]`. -/
def geometricEdge (δ θ : ℝ) : Space :=
  ((1 + δ * Real.sin θ) * Real.cos (2 * θ),
   (1 + δ * Real.sin θ) * Real.sin (2 * θ), -δ * Real.cos θ)

theorem geometricEdge_closed (δ : ℝ) : geometricEdge δ 0 = geometricEdge δ (2 * Real.pi) := by
  norm_num [geometricEdge, Real.sin_two_mul, Real.cos_two_mul]

theorem geometricEdge_first_half (δ t : ℝ) : geometricEdge δ (Real.pi * t) = edge1 δ t := by
  rw [edge1_full]
  simp [geometricEdge, mobiusSquare, mobius]

theorem geometricEdge_second_half (δ t : ℝ) :
    geometricEdge δ (Real.pi + Real.pi * t) = reverse (edge3 δ) t := by
  rw [edge3_full]
  ext <;> simp [geometricEdge, mobiusSquare, mobius, reverse, Real.sin_add, Real.cos_add,
    mul_add, Real.sin_two_mul, Real.cos_two_mul] <;> norm_num [sub_eq_add_neg]

/-- Each point of the source has a positive planar radius. -/
theorem radius_positive {δ θ t : ℝ} (hδ : δ < 1) (ht : t ∈ Icc (-δ) δ) :
    0 < 1 - t * Real.sin θ := by
  have ha : |t| ≤ δ := abs_le.mpr ht
  have hb : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : |t * Real.sin θ| ≤ δ := by
    rw [abs_mul]
    calc
      |t| * |Real.sin θ| ≤ |t| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ δ := by simpa using ha
  linarith [(le_abs_self (t * Real.sin θ)).trans hc]

/-- The entire band avoids the axis where the angular form is undefined. -/
theorem avoids_axis {δ : ℝ} (hδ : δ < 1) {q : Space} (hq : q ∈ band δ) :
    q.1 ^ 2 + q.2.1 ^ 2 > 0 := by
  obtain ⟨⟨θ,t⟩, h, rfl⟩ := hq
  have hr := radius_positive (θ := θ) hδ h.2
  have he : (phi (θ,t)).1 ^ 2 + (phi (θ,t)).2.1 ^ 2 = (1-t*Real.sin θ)^2 := by
    dsimp [phi, mobius]
    nlinarith [Real.sin_sq_add_cos_sq (2*θ)]
  rw [he]
  positivity

/-- Equality of image points has exactly the seam identifications and no others. -/
theorem injective_modulo_seam {δ : ℝ} (hδ : δ < 1)
    {θ t ψ u : ℝ} (hθ : θ ∈ Icc 0 Real.pi) (ht : t ∈ Icc (-δ) δ)
    (hψ : ψ ∈ Icc 0 Real.pi) (hu : u ∈ Icc (-δ) δ)
    (he : phi (θ,t) = phi (ψ,u)) :
    (θ = ψ ∧ t = u) ∨ (θ = 0 ∧ ψ = Real.pi ∧ t = -u) ∨
      (θ = Real.pi ∧ ψ = 0 ∧ t = -u) := by
  have hx := congrArg Prod.fst he
  have hy := congrArg (fun q : Space => q.2.1) he
  have hz := congrArg (fun q : Space => q.2.2) he
  dsimp [phi, mobius] at hx hy hz
  have hr := radius_positive (θ := θ) hδ ht
  have hs := radius_positive (θ := ψ) hδ hu
  have hnorm (α v : ℝ) :
      ((1-v*Real.sin α)*Real.cos (2*α))^2 +
      ((1-v*Real.sin α)*Real.sin (2*α))^2 = (1-v*Real.sin α)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2*α)]
  have hradius : 1-t*Real.sin θ = 1-u*Real.sin ψ := by
    have hn := hnorm θ t
    rw [hx, hy, hnorm] at hn
    nlinarith
  have hcos : Real.cos (2*θ) = Real.cos (2*ψ) := by
    rw [hradius] at hx
    exact mul_left_cancel₀ hs.ne' hx
  have hsin : Real.sin (2*θ) = Real.sin (2*ψ) := by
    rw [hradius] at hy
    exact mul_left_cancel₀ hs.ne' hy
  have hd : Real.cos (2 * (θ-ψ)) = 1 := by
    rw [mul_sub, Real.cos_sub, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (2*ψ)]
  by_cases hplus : θ-ψ = Real.pi
  · right; right
    have hθ' : θ = Real.pi := by linarith [hψ.1, hθ.2]
    have hψ' : ψ = 0 := by linarith [hψ.1, hθ.2]
    refine ⟨hθ', hψ', ?_⟩
    rw [hθ', hψ'] at hz
    simpa using (neg_eq_iff_eq_neg.mp (by simpa using hz : -t = u))
  by_cases hminus : θ-ψ = -Real.pi
  · right; left
    have hθ' : θ = 0 := by linarith [hθ.1, hψ.2]
    have hψ' : ψ = Real.pi := by linarith [hθ.1, hψ.2]
    refine ⟨hθ', hψ', ?_⟩
    simpa [hθ', hψ'] using hz
  have hsame : θ = ψ := by
    have hzero := (Real.cos_eq_one_iff_of_lt_of_lt
      (show -(2*Real.pi) < 2*(θ-ψ) by
        have : -Real.pi < θ-ψ := lt_of_le_of_ne (by linarith [hθ.1,hψ.2]) (Ne.symm hminus)
        linarith)
      (show 2*(θ-ψ) < 2*Real.pi by
        have : θ-ψ < Real.pi := lt_of_le_of_ne (by linarith [hθ.2,hψ.1]) hplus
        linarith)).mp hd
    linarith
  left
  refine ⟨hsame, ?_⟩
  subst ψ
  have hss : (t-u)*Real.sin θ = 0 := by linarith
  have hcc : (t-u)*Real.cos θ = 0 := by nlinarith [hz]
  by_contra htu
  have hn : t-u ≠ 0 := sub_ne_zero.mpr htu
  have hs0 := (mul_eq_zero.mp hss).resolve_left hn
  have hc0 := (mul_eq_zero.mp hcc).resolve_left hn
  have hunit := Real.sin_sq_add_cos_sq θ
  simp [hs0,hc0] at hunit

def dot (v w : Space) : ℝ := v.1*w.1 + v.2.1*w.2.1 + v.2.2*w.2.2

/-- A geometric orientation is a continuous nowhere-zero normal field on the
actual image. Orthogonality refers to derivatives of the full source map. -/
def HasNormalOrientation (δ : ℝ) : Prop :=
  ∃ N : Space → Space, ContinuousOn N (band δ) ∧
    (∀ q ∈ band δ, N q ≠ 0) ∧
    (∀ p ∈ source δ,
      dot (N (phi p)) (deriv (fun θ => phi (θ,p.2)) p.1) = 0 ∧
      dot (N (phi p)) (deriv (fun t => phi (p.1,t)) p.2) = 0)

def core (θ : ℝ) : Space := (Real.cos (2*θ), Real.sin (2*θ), 0)
def coreNormal (θ : ℝ) : Space :=
  (Real.cos θ * Real.cos (2*θ), Real.cos θ * Real.sin (2*θ), Real.sin θ)

theorem core_eq (θ : ℝ) : phi (θ,0) = core θ := by simp [phi,mobius,core]

theorem core_theta_derivative (θ : ℝ) :
    HasDerivAt (fun s => phi (s,0))
      (-2*Real.sin (2*θ), 2*Real.cos (2*θ), 0) θ := by
  simp only [core_eq, core]
  convert (((Real.hasDerivAt_cos (2*θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).prodMk
    (((Real.hasDerivAt_sin (2*θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).prodMk
      (hasDerivAt_const θ (0 : ℝ)))) using 1 <;> simp [mul_comm]

theorem core_t_derivative (θ : ℝ) :
    HasDerivAt (fun t => phi (θ,t))
      (-Real.sin θ*Real.cos (2*θ), -Real.sin θ*Real.sin (2*θ), Real.cos θ) 0 := by
  have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).mul_const (Real.sin θ))
  convert (h.mul_const (Real.cos (2*θ))).prodMk
    ((h.mul_const (Real.sin (2*θ))).prodMk
      ((hasDerivAt_id (0 : ℝ)).mul_const (Real.cos θ))) using 1 <;>
    simp [phi,mobius]

/-- Any vector normal to the two actual core tangents is a multiple of the
specified unit normal. This is a linear-algebra fact, not a gluing axiom. -/
theorem core_normal_multiple (θ : ℝ) (v : Space)
    (h1 : dot v (-2*Real.sin (2*θ), 2*Real.cos (2*θ), 0) = 0)
    (h2 : dot v (-Real.sin θ*Real.cos (2*θ), -Real.sin θ*Real.sin (2*θ), Real.cos θ) = 0) :
    v = dot v (coreNormal θ) • coreNormal θ := by
  dsimp [dot] at h1 h2
  have hsc := Real.sin_sq_add_cos_sq θ
  have hsc2 := Real.sin_sq_add_cos_sq (2*θ)
  have hr1 : v.1 = (v.1*Real.cos (2*θ)+v.2.1*Real.sin (2*θ))*Real.cos (2*θ) := by
    nlinarith [congrArg (fun x : ℝ => x*Real.sin (2*θ)) h1,
      congrArg (fun x : ℝ => v.1*x) hsc2]
  have hr2 : v.2.1 = (v.1*Real.cos (2*θ)+v.2.1*Real.sin (2*θ))*Real.sin (2*θ) := by
    nlinarith [congrArg (fun x : ℝ => x*Real.cos (2*θ)) h1,
      congrArg (fun x : ℝ => v.2.1*x) hsc2]
  have ha : v.1*Real.cos (2*θ)+v.2.1*Real.sin (2*θ) =
      dot v (coreNormal θ)*Real.cos θ := by
    dsimp [dot,coreNormal]
    nlinarith [congrArg (fun x : ℝ => x*Real.sin θ) h2,
      congrArg (fun x : ℝ => (v.1*Real.cos (2*θ)+v.2.1*Real.sin (2*θ))*x) hsc]
  have hz : v.2.2 = dot v (coreNormal θ)*Real.sin θ := by
    dsimp [dot,coreNormal]
    nlinarith [congrArg (fun x : ℝ => x*Real.cos θ) h2,
      congrArg (fun x : ℝ => v.2.2*x) hsc]
  apply Prod.ext
  · change v.1 = dot v (coreNormal θ) * (Real.cos θ * Real.cos (2*θ))
    rw [hr1, ha]; ring
  · apply Prod.ext
    · change v.2.1 = dot v (coreNormal θ) * (Real.cos θ * Real.sin (2*θ))
      rw [hr2, ha]; ring
    · exact hz

/-- The actual band admits no continuous nowhere-zero normal field. -/
theorem nonorientable {δ : ℝ} (hδ : 0 < δ) : ¬ HasNormalOrientation δ := by
  rintro ⟨N,hN,hn,horth⟩
  have hmem (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) : core θ ∈ band δ := by
    exact ⟨(θ,0), ⟨hθ,⟨by linarith, hδ.le⟩⟩, core_eq θ⟩
  let f : ℝ → ℝ := fun θ => dot (N (core θ)) (coreNormal θ)
  have hc : ContinuousOn f (Icc 0 Real.pi) := by
    have hcore : Continuous core := by unfold core; fun_prop
    have hcomp : ContinuousOn (fun θ => N (core θ)) (Icc 0 Real.pi) :=
      hN.comp hcore.continuousOn hmem
    exact ((hcomp.fst.mul (by fun_prop)).add
      (hcomp.snd.fst.mul (by fun_prop))).add (hcomp.snd.snd.mul (by fun_prop))
  have hf (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) : f θ ≠ 0 := by
    have ho := horth (θ,0) ⟨hθ,⟨by linarith, hδ.le⟩⟩
    rw [(core_theta_derivative θ).deriv, (core_t_derivative θ).deriv, core_eq] at ho
    have hm := core_normal_multiple θ (N (core θ)) ho.1 ho.2
    intro he
    have he' : dot (N (core θ)) (coreNormal θ) = 0 := he
    rw [he', zero_smul] at hm
    exact hn _ (hmem θ hθ) hm
  have hend : f Real.pi = -f 0 := by
    norm_num [f,dot,core,coreNormal,Real.sin_two_mul,Real.cos_two_mul]
  have hsign := (isPreconnected_Icc.image _ hc).ordConnected
  have h0 : f 0 ∈ f '' Icc 0 Real.pi := mem_image_of_mem _ ⟨le_rfl,Real.pi_pos.le⟩
  have hπ : f Real.pi ∈ f '' Icc 0 Real.pi := mem_image_of_mem _ ⟨Real.pi_pos.le,le_rfl⟩
  have hz : (0 : ℝ) ∈ f '' Icc 0 Real.pi := by
    rcases le_total (f 0) 0 with hle | hge
    · exact hsign.out h0 hπ ⟨hle, by linarith [hend]⟩
    · exact hsign.out hπ h0 ⟨by linarith [hend],hge⟩
  obtain ⟨θ,hθ,hzero⟩ := hz
  exact hf θ hθ hzero

open MeasureTheory

/-- The ordinary planar projection, as a continuous real linear map. -/
def planar : Space →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

@[simp] theorem planar_apply (q : Space) : planar q = ⟨q.1,q.2.1⟩ := rfl

def eta : SimplexIntegration.Form 1 Space := SimplexIntegration.pullback Exercise21.eta planar

theorem eta_coefficient (q v : Space) : PathIntegration.fromAlternating eta q v =
    (q.1*v.2.1-q.2.1*v.1)/(q.1^2+q.2.1^2) := by
  change Exercise21.eta (planar q) (fun _ => fderiv ℝ planar q v) = _
  rw [planar.fderiv]
  exact Exercise21.etaLinear_apply _ _

theorem eta_closed {q : Space} (hq : planar q ≠ 0) : extDeriv eta q = 0 := by
  rw [eta, SimplexIntegration.exterior_pullback]
  · ext v
    change extDeriv Exercise21.eta (planar q) (fun i => fderiv ℝ planar q (v i)) = 0
    rw [Exercise21.eta_closed hq]
    rfl
  · exact (Exercise21.eta_smooth.differentiableOn (by norm_num) _ hq).differentiableAt
      (isOpen_ne.mem_nhds hq)
  · exact planar.contDiff.contDiffAt

theorem eta_smooth : ContDiffOn ℝ 1 eta {q | planar q ≠ 0} := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  exact SimplexStokes.pullback_contDiffAt
    (Exercise21.eta_smooth.contDiffAt (isOpen_ne.mem_nhds hq)) planar.contDiff.contDiffAt

/-- Stokes gives zero on the actual parameter boundary, with both seam copies. -/
theorem parametrized_boundary_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    PathIntegration.chainIntegral (PathIntegration.fromAlternating eta)
      (surfaceBoundary (surface (mobiusSquare δ))) = 0 := by
  apply Exercise21.closed_square_boundary eta (mobiusSquare δ) isOpen_univ (subset_univ _)
    (SmoothChains.mobiusSquare_smooth δ).contDiffOn
    (isOpen_ne.preimage planar.continuous) eta_smooth _ (fun _ => eta_closed)
  intro p hp hzero
  have hsrc : (Real.pi*p.1,δ*(2*p.2-1)) ∈ source δ := by
    constructor <;> constructor
    · exact mul_nonneg Real.pi_pos.le hp.1.1
    · nlinarith [hp.1.2,Real.pi_pos]
    · nlinarith [hp.2.1]
    · nlinarith [hp.2.2]
  have ha := avoids_axis hδ1 (show mobiusSquare δ p ∈ band δ from
    ⟨_,hsrc,rfl⟩)
  have hx := congrArg Complex.re hzero
  have hy := congrArg Complex.im hzero
  change (mobiusSquare δ p).1 = 0 at hx
  change (mobiusSquare δ p).2.1 = 0 at hy
  rw [hx,hy] at ha
  norm_num at ha

/-- Scalar radius changes do not change the angular pullback coefficient. -/
theorem angular_radial (z v : ℂ) (r d : ℝ) (hz : z ≠ 0) (hr : r ≠ 0) :
    Exercise21.etaLinear (r • z) (r • v + d • z) = Exercise21.etaLinear z v := by
  rw [Exercise21.eta_eq_im_div,Exercise21.eta_eq_im_div]
  have he : (r • v + d • z) / (r • z) = v/z + ((d/r : ℝ) : ℂ) := by
    simp only [Complex.real_smul,Complex.ofReal_div]
    field_simp [hz,Complex.ofReal_ne_zero.mpr hr]
  rw [he]
  simp

/-- A radial curve with angular speed `k` has the constant angular coefficient `k`. -/
theorem polar_coefficient (ρ : ℝ → ℝ) (k t d : ℝ)
    (hρ : HasDerivAt ρ d t) (hr : ρ t ≠ 0) :
    PathIntegration.coefficient Exercise21.etaLinear
      (fun s => ρ s • Exercise21.circle 1 (k*s)) t = k := by
  have hc := (Exercise21.circle_derivative 1 (k*t)).scomp t ((hasDerivAt_id t).const_mul k)
  have hd := hρ.smul hc
  simp only [Function.comp_def,mul_one] at hd
  change HasDerivAt (fun s => ρ s • Exercise21.circle 1 (k*s))
    (ρ t • (k • Exercise21.circleVelocity 1 (k*t)) + d • Exercise21.circle 1 (k*t)) t at hd
  rw [PathIntegration.coefficient,hd.deriv]
  rw [angular_radial _ _ _ _ (Exercise21.circle_nonzero (by norm_num) _) hr,
    map_smul,Exercise21.circle_coefficient (by norm_num)]
  simp

theorem projection_coefficient (p : ℝ → Space) (t : ℝ) (hp : DifferentiableAt ℝ p t) :
    PathIntegration.coefficient (PathIntegration.fromAlternating eta) p t =
      PathIntegration.coefficient Exercise21.etaLinear (planar ∘ p) t := by
  have hd := planar.hasFDerivAt.comp_hasDerivAt t hp.hasDerivAt
  change Exercise21.etaLinear (planar (p t)) (fderiv ℝ planar (p t) (deriv p t)) =
    Exercise21.etaLinear (planar (p t)) (deriv (planar ∘ p) t)
  rw [hd.deriv,planar.fderiv]

theorem edge1_projection (δ : ℝ) : planar ∘ edge1 δ =
    fun t => (1+δ*Real.sin (Real.pi*t)) • Exercise21.circle 1 (2*Real.pi*t) := by
  rw [edge1_full]
  funext t
  apply Complex.ext <;> simp only [Function.comp_apply,planar_apply,mobiusSquare,mobius,
    Exercise21.circle,Complex.smul_re,Complex.smul_im,smul_eq_mul,mul_zero,zero_sub,
    mul_neg_one,neg_mul,sub_neg_eq_add,one_mul,mul_assoc]

theorem top_projection (δ : ℝ) : planar ∘ (fun t => mobiusSquare δ (t,1)) =
    fun t => (1-δ*Real.sin (Real.pi*t)) • Exercise21.circle 1 (2*Real.pi*t) := by
  funext t
  apply Complex.ext <;> simp only [Function.comp_apply,planar_apply,mobiusSquare,mobius,
    Exercise21.circle,Complex.smul_re,Complex.smul_im,smul_eq_mul,mul_one,
    show (2 : ℝ)-1=1 by norm_num,one_mul,mul_assoc]

theorem edge1_smooth (δ : ℝ) : ContDiff ℝ 2 (edge1 δ) := by
  rw [edge1_full]
  exact (SmoothChains.mobiusSquare_smooth δ).comp (contDiff_id.prodMk contDiff_const)

theorem top_smooth (δ : ℝ) : ContDiff ℝ 2 (fun t => mobiusSquare δ (t,1)) :=
  (SmoothChains.mobiusSquare_smooth δ).comp (contDiff_id.prodMk contDiff_const)

theorem edge1_angular_coefficient {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℝ) :
    PathIntegration.coefficient (PathIntegration.fromAlternating eta) (edge1 δ) t = 2*Real.pi := by
  rw [projection_coefficient _ _ ((edge1_smooth δ).differentiable (by norm_num) t),edge1_projection]
  apply polar_coefficient
  · exact (hasDerivAt_const t (1 : ℝ)).add
      (((Real.hasDerivAt_sin (Real.pi*t)).comp t ((hasDerivAt_id t).const_mul Real.pi)).const_mul δ)
  · have hr := radius_positive (θ := Real.pi*t) hδ1
      (show -δ ∈ Icc (-δ) δ from ⟨le_rfl,by linarith⟩)
    simpa using hr.ne'

theorem top_angular_coefficient {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℝ) :
    PathIntegration.coefficient (PathIntegration.fromAlternating eta)
      (fun s => mobiusSquare δ (s,1)) t = 2*Real.pi := by
  rw [projection_coefficient _ _ ((top_smooth δ).differentiable (by norm_num) t),top_projection]
  apply polar_coefficient
  · exact (hasDerivAt_const t (1 : ℝ)).sub
      (((Real.hasDerivAt_sin (Real.pi*t)).comp t ((hasDerivAt_id t).const_mul Real.pi)).const_mul δ)
  · exact (radius_positive (θ := Real.pi*t) hδ1 ⟨by linarith,le_rfl⟩).ne'

theorem edge1_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    PathIntegration.pathIntegral (PathIntegration.fromAlternating eta) (edge1 δ) = 2*Real.pi := by
  simp [PathIntegration.pathIntegral,edge1_angular_coefficient hδ hδ1]

theorem edge3_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    PathIntegration.pathIntegral (PathIntegration.fromAlternating eta) (edge3 δ) = -(2*Real.pi) := by
  rw [edge3_full,PathIntegration.pathIntegral_reverse]
  simp [PathIntegration.pathIntegral,top_angular_coefficient hδ hδ1]

/-- The two rim arcs form the geometric edge chain; the seam is not included. -/
def geometricEdgeChain (δ : ℝ) : PathChain Space := path (edge1 δ) - path (edge3 δ)

theorem geometric_edge_chain_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    PathIntegration.chainIntegral (PathIntegration.fromAlternating eta) (geometricEdgeChain δ) =
      4*Real.pi := by
  rw [geometricEdgeChain,map_sub,PathIntegration.chainIntegral_path,PathIntegration.chainIntegral_path,
    edge1_integral hδ hδ1,edge3_integral hδ hδ1]
  ring

theorem geometric_edge_ne_parameter_boundary {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    geometricEdgeChain δ ≠ surfaceBoundary (surface (mobiusSquare δ)) := by
  intro he
  have hh := congrArg (PathIntegration.chainIntegral (PathIntegration.fromAlternating eta)) he
  rw [geometric_edge_chain_integral hδ hδ1,parametrized_boundary_integral hδ hδ1] at hh
  exact (mul_ne_zero (by norm_num) Real.pi_ne_zero) hh

theorem edge_endpoints (δ : ℝ) :
    edge1 δ 0 = a δ ∧ edge1 δ 1 = b δ ∧ edge3 δ 0 = a δ ∧ edge3 δ 1 = b δ := by
  simpa only [edge1,edge3,Function.comp_apply,OrientedChains.Parametric.segment,
    sub_zero,one_smul,zero_smul,add_zero,sub_self,zero_add] using
    ⟨(corner_images δ).1,(corner_images δ).2.2.1,(corner_images δ).2.1,(corner_images δ).2.2.2⟩

theorem edge3_smooth (δ : ℝ) : ContDiff ℝ 2 (edge3 δ) := by
  rw [edge3_full]
  exact (top_smooth δ).comp (contDiff_const.sub contDiff_id)

theorem edge_mem_band {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    edge1 δ t ∈ band δ ∧ edge3 δ t ∈ band δ := by
  rw [edge1_full,edge3_full]
  constructor
  · refine ⟨(Real.pi*t,-δ),⟨?_,⟨le_rfl,by linarith⟩⟩,?_⟩
    · exact ⟨mul_nonneg Real.pi_pos.le ht.1,mul_le_of_le_one_right Real.pi_pos.le ht.2⟩
    · simp [mobiusSquare]
  · refine ⟨(Real.pi*(1-t),δ),⟨?_,⟨by linarith,le_rfl⟩⟩,?_⟩
    · constructor <;> nlinarith [Real.pi_pos,ht.1,ht.2]
    · norm_num [mobiusSquare,reverse]

theorem projection_nonzero {δ : ℝ} (hδ1 : δ < 1) {q : Space} (hq : q ∈ band δ) :
    planar q ≠ 0 := by
  intro hh
  have hx := congrArg Complex.re hh
  have hy := congrArg Complex.im hh
  have ha := avoids_axis hδ1 hq
  change q.1 = 0 at hx
  change q.2.1 = 0 at hy
  simp [hx,hy] at ha

/-- A source-valid projected loop, including the genuine C¹ derivative jet. -/
theorem projected_loop (p : ℝ → Space) (hp : ContDiff ℝ 2 p)
    (hc : planar (p 0) = planar (p 1))
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, planar (p t) ≠ 0) :
    Rudin.Chapter08.IsC1NonzeroLoop (planar ∘ p) (deriv (planar ∘ p)) 0 1 := by
  have h := planar.contDiff.comp hp
  refine ⟨by norm_num,hc,fun t _ => (h.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt,
    ?_,hn⟩
  exact (h.continuous_deriv (by norm_num)).continuousOn

/-- The first spiraling edge has the actual Chapter 8 winding index `+1`. -/
theorem first_edge_winding {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Rudin.Chapter08.curveIndex (planar ∘ edge1 δ) (deriv (planar ∘ edge1 δ)) 0 1 = 1 := by
  have hl := projected_loop (edge1 δ) (edge1_smooth δ)
    (by rw [(edge_endpoints δ).1,(edge_endpoints δ).2.1]; rfl)
    (fun t ht => projection_nonzero hδ1 (edge_mem_band hδ ht).1)
  have hw := Exercise21.winding_index hl
  have hi : Exercise21.angularIntegral (planar ∘ edge1 δ) (deriv (planar ∘ edge1 δ)) 0 1 =
      2*Real.pi := by
    change PathIntegration.pathIntegral Exercise21.etaLinear (planar ∘ edge1 δ) = _
    have he := edge1_integral hδ hδ1
    rw [← he]
    apply intervalIntegral.integral_congr
    intro t _
    exact (projection_coefficient _ _ ((edge1_smooth δ).differentiable (by norm_num) t)).symm
  rw [hi,div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)] at hw
  exact hw.symm

/-- The third spiraling edge has the actual Chapter 8 winding index `-1`. -/
theorem third_edge_winding {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Rudin.Chapter08.curveIndex (planar ∘ edge3 δ) (deriv (planar ∘ edge3 δ)) 0 1 = -1 := by
  have hl := projected_loop (edge3 δ) (edge3_smooth δ)
    (by rw [(edge_endpoints δ).2.2.1,(edge_endpoints δ).2.2.2]; rfl)
    (fun t ht => projection_nonzero hδ1 (edge_mem_band hδ ht).2)
  have hw := Exercise21.winding_index hl
  have hi : Exercise21.angularIntegral (planar ∘ edge3 δ) (deriv (planar ∘ edge3 δ)) 0 1 =
      -(2*Real.pi) := by
    change PathIntegration.pathIntegral Exercise21.etaLinear (planar ∘ edge3 δ) = _
    have he := edge3_integral hδ hδ1
    rw [← he]
    apply intervalIntegral.integral_congr
    intro t _
    exact (projection_coefficient _ _ ((edge3_smooth δ).differentiable (by norm_num) t)).symm
  rw [hi,neg_div,div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)] at hw
  simpa using hw.symm

/-- The rim is the image of the two free edges of the rectangle. The glued
vertical edges are not free edges. -/
def rim (δ : ℝ) : Set Space :=
  {q | ∃ θ ∈ Icc 0 Real.pi, q = phi (θ,-δ) ∨ q = phi (θ,δ)}

theorem geometricEdge_lower (δ θ : ℝ) : geometricEdge δ θ = phi (θ,-δ) := by
  simp [geometricEdge,phi,mobius]

theorem geometricEdge_upper (δ θ : ℝ) : geometricEdge δ (Real.pi+θ) = phi (θ,δ) := by
  ext <;> norm_num [geometricEdge,phi,mobius,Real.sin_add,Real.cos_add,mul_add,
    Real.sin_two_mul,Real.cos_two_mul,sub_eq_add_neg]

/-- The complete range of the closed parameterization is exactly the free rim,
not the image of the whole rectangle boundary (which includes the seam). -/
theorem geometric_edge_range (δ : ℝ) :
    geometricEdge δ '' Icc 0 (2*Real.pi) = rim δ := by
  ext q
  constructor
  · rintro ⟨θ,hθ,rfl⟩
    by_cases hle : θ ≤ Real.pi
    · exact ⟨θ,⟨hθ.1,hle⟩,Or.inl (geometricEdge_lower δ θ)⟩
    · refine ⟨θ-Real.pi,⟨by linarith,by linarith [hθ.2]⟩,Or.inr ?_⟩
      convert geometricEdge_upper δ (θ-Real.pi) using 1
      congr 1
      ring
  · rintro ⟨θ,hθ,he | he⟩
    · exact ⟨θ,⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩,(geometricEdge_lower δ θ).trans he.symm⟩
    · exact ⟨Real.pi+θ,⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2]⟩,
        (geometricEdge_upper δ θ).trans he.symm⟩

theorem rim_subset_band {δ : ℝ} (hδ : 0 < δ) : rim δ ⊆ band δ := by
  rintro q ⟨θ,hθ,hq | hq⟩
  · exact ⟨(θ,-δ),⟨hθ,⟨le_rfl,by linarith⟩⟩,hq.symm⟩
  · exact ⟨(θ,δ),⟨hθ,⟨by linarith,le_rfl⟩⟩,hq.symm⟩

theorem geometricEdge_smooth (δ : ℝ) : ContDiff ℝ 2 (geometricEdge δ) := by
  unfold geometricEdge
  fun_prop

theorem geometricEdge_projection (δ : ℝ) : planar ∘ geometricEdge δ =
    fun t => (1+δ*Real.sin t) • Exercise21.circle 1 (2*t) := by
  funext t
  apply Complex.ext <;> simp only [Function.comp_apply,planar_apply,geometricEdge,
    Exercise21.circle,Complex.smul_re,Complex.smul_im,smul_eq_mul,one_mul]

theorem geometricEdge_coefficient {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℝ) :
    PathIntegration.coefficient (PathIntegration.fromAlternating eta) (geometricEdge δ) t = 2 := by
  rw [projection_coefficient _ _ ((geometricEdge_smooth δ).differentiable (by norm_num) t),
    geometricEdge_projection]
  apply polar_coefficient
  · exact (hasDerivAt_const t (1 : ℝ)).add ((Real.hasDerivAt_sin t).const_mul δ)
  · have hr := radius_positive (θ := t) hδ1
      (show -δ ∈ Icc (-δ) δ from ⟨le_rfl,by linarith⟩)
    simpa using hr.ne'

/-- The integral on the exact closed parameterization in the book is `4π`. -/
theorem geometric_edge_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (∫ t in (0 : ℝ)..2*Real.pi,
      PathIntegration.coefficient (PathIntegration.fromAlternating eta) (geometricEdge δ) t) =
      4*Real.pi := by
  simp [geometricEdge_coefficient hδ hδ1]
  ring

/-- The literal real Riemann integral exists and has the same `4π` value. -/
theorem geometric_edge_source_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) (geometricEdge δ))
      id 0 (2*Real.pi) (4*Real.pi) := by
  have hc : ContinuousOn
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) (geometricEdge δ))
      (Icc 0 (2*Real.pi)) := by
    have he := funext (geometricEdge_coefficient hδ hδ1)
    rw [he]
    exact continuousOn_const
  have hb := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id (by positivity : 0 ≤ 2*Real.pi) hc
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id,geometric_edge_integral hδ hδ1] using hb

def thetaTangent (θ t : ℝ) : Space :=
  (-t*Real.cos θ*Real.cos (2*θ)-2*(1-t*Real.sin θ)*Real.sin (2*θ),
   -t*Real.cos θ*Real.sin (2*θ)+2*(1-t*Real.sin θ)*Real.cos (2*θ),-t*Real.sin θ)
def transverseTangent (θ : ℝ) : Space :=
  (-Real.sin θ*Real.cos (2*θ),-Real.sin θ*Real.sin (2*θ),Real.cos θ)

theorem theta_derivative (θ t : ℝ) :
    HasDerivAt (fun s => phi (s,t)) (thetaTangent θ t) θ := by
  have hR := (hasDerivAt_const θ (1 : ℝ)).sub ((Real.hasDerivAt_sin θ).const_mul t)
  have hc := (Real.hasDerivAt_cos (2*θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hs := (Real.hasDerivAt_sin (2*θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  convert (hR.mul hc).prodMk ((hR.mul hs).prodMk ((Real.hasDerivAt_cos θ).const_mul t)) using 1
  · rfl
  · ext <;> dsimp [thetaTangent] <;> ring

theorem transverse_derivative (θ t : ℝ) :
    HasDerivAt (fun s => phi (θ,s)) (transverseTangent θ) t := by
  have hR := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const (Real.sin θ))
  convert (hR.mul_const (Real.cos (2*θ))).prodMk
    ((hR.mul_const (Real.sin (2*θ))).prodMk ((hasDerivAt_id t).mul_const (Real.cos θ))) using 1
  · rfl
  · ext <;> simp [transverseTangent]

/-- The source map is regular everywhere on the band: its two actual tangent
vectors are linearly independent, including the seam and the free rim. -/
theorem tangent_independence {δ θ t : ℝ} (hδ1 : δ < 1) (ht : t ∈ Icc (-δ) δ)
    (α β : ℝ) (he : α • deriv (fun s => phi (s,t)) θ +
      β • deriv (fun s => phi (θ,s)) t = 0) : α = 0 ∧ β = 0 := by
  rw [(theta_derivative θ t).deriv,(transverse_derivative θ t).deriv] at he
  have hx := congrArg Prod.fst he
  have hy := congrArg (fun q : Space => q.2.1) he
  have hz := congrArg (fun q : Space => q.2.2) he
  dsimp [thetaTangent,transverseTangent] at hx hy hz
  have hunit := Real.sin_sq_add_cos_sq (2*θ)
  have hα : α*(2*(1-t*Real.sin θ)) = 0 := by
    nlinarith [congrArg (fun a : ℝ => a*Real.sin (2*θ)) hx,
      congrArg (fun a : ℝ => a*Real.cos (2*θ)) hy,
      congrArg (fun a : ℝ => α*(2*(1-t*Real.sin θ))*a) hunit]
  have hα0 : α = 0 := (mul_eq_zero.mp hα).resolve_right
    (mul_ne_zero (by norm_num) (radius_positive (θ := θ) hδ1 ht).ne')
  refine ⟨hα0,?_⟩
  subst α
  simp only [zero_smul,zero_add] at he
  by_contra hβ
  have hv : transverseTangent θ = 0 := (smul_eq_zero.mp he).resolve_left hβ
  have hcz := congrArg (fun q : Space => q.2.2) hv
  have hcx := congrArg Prod.fst hv
  have hcy := congrArg (fun q : Space => q.2.1) hv
  dsimp [transverseTangent] at hcz hcx hcy
  have hs : Real.sin θ ≠ 0 := by
    intro hs
    have hh := Real.sin_sq_add_cos_sq θ
    simp [hs,hcz] at hh
  have hc2 : Real.cos (2*θ) = 0 := (mul_eq_zero.mp hcx).resolve_left (neg_ne_zero.mpr hs)
  have hs2 : Real.sin (2*θ) = 0 := (mul_eq_zero.mp hcy).resolve_left (neg_ne_zero.mpr hs)
  simp [hc2,hs2] at hunit

theorem seam_coefficient (δ t : ℝ) :
    PathIntegration.coefficient (PathIntegration.fromAlternating eta) (edge2 δ) t = 0 := by
  rw [(repeated_seam_maps δ).1]
  simp only [PathIntegration.coefficient,(PathIntegration.segment_hasDerivAt (b δ) (a δ) t).deriv,
    eta_coefficient]
  simp [OrientedChains.Parametric.segment,a,b]

theorem constant_coefficient_source (p : ℝ → Space) (c : ℝ)
    (hc : ∀ t, PathIntegration.coefficient (PathIntegration.fromAlternating eta) p t = c) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) p) id 0 1 c := by
  have he := funext hc
  have hcont : ContinuousOn (PathIntegration.coefficient (PathIntegration.fromAlternating eta) p)
      (Icc 0 1) := by rw [he]; exact continuousOn_const
  have h := PathIntegration.darboux_path_bridge (PathIntegration.fromAlternating eta) p hcont
  simpa only [PathIntegration.pathIntegral,he,intervalIntegral.integral_const,
    sub_zero,one_smul] using h

/-- Every oriented edge integral in the Stokes sum has its actual source
Riemann value. Both copies of the seam have value zero. -/
theorem boundary_source_integrals {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) (edge1 δ))
      id 0 1 (2*Real.pi) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) (edge2 δ))
      id 0 1 0 ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) (edge3 δ))
      id 0 1 (-(2*Real.pi)) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (PathIntegration.coefficient (PathIntegration.fromAlternating eta) (edge4 δ))
      id 0 1 0 := by
  refine ⟨constant_coefficient_source _ _ (edge1_angular_coefficient hδ hδ1),
    constant_coefficient_source _ _ (seam_coefficient δ),
    constant_coefficient_source _ _ ?_,constant_coefficient_source _ _ ?_⟩
  · intro t
    rw [edge3_full,PathIntegration.coefficient_reverse,top_angular_coefficient hδ hδ1]
  · intro t
    rw [(repeated_seam_maps δ).2,← (repeated_seam_maps δ).1]
    exact seam_coefficient δ t

end Rudin.Chapter10.Exercise32
