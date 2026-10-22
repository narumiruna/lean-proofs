module

public import Math.Rudin.Chapter06.Exercise10

/-!
# Chapter 6, Exercise 11

Source: Rudin, page 140 (PDF page 149).
The weighted L² quantity is a seminorm on actual functions. The proof uses
Schwarz, and does not identify functions whose difference has integral zero.
-/

@[expose] public section

noncomputable section

namespace Rudin.Chapter06

open Set
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesIntegralLaws
open Rudin.Support.StieltjesComposition Rudin.Support.StieltjesComplex

/-- The unique raw integral value when it exists. All uses below prove existence. -/
def rawRSValue (f α : ℝ → ℝ) (a b : ℝ) : ℝ := by
  classical
  exact if h : ∃ value, HasRSIntegral f α a b value then h.choose else 0

theorem rawRSValue_eq {f α : ℝ → ℝ} {a b value : ℝ}
    (hf : HasRSIntegral f α a b value) : rawRSValue f α a b = value := by
  unfold rawRSValue
  rw [dite_eq_left ⟨value, hf⟩]
  exact Rudin.Support.StieltjesRefinement.hasRSIntegral_unique
    (Exists.choose_spec _) hf

/-- Rudin's L² seminorm, on functions rather than almost-everywhere classes. -/
def rsL2Norm (α : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (rawRSValue (fun x => ‖f x‖ ^ 2) α a b)

/-- Squared norms have an actual raw integral. -/
theorem exists_l2_integral {a b : ℝ} {f : ℝ → ℂ} {α : ℝ → ℝ} {z : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b z) :
    ∃ value, HasRSIntegral (fun x => ‖f x‖ ^ 2) α a b value := by
  simpa only [Real.rpow_two] using exists_complex_norm_rpow hab hf (p := 2) (by norm_num)

theorem rsL2Norm_eq {a b value : ℝ} {f : ℝ → ℂ} {α : ℝ → ℝ}
    (hf : HasRSIntegral (fun x => ‖f x‖ ^ 2) α a b value) :
    rsL2Norm α a b f = Real.sqrt value := by
  rw [rsL2Norm, rawRSValue_eq hf]

theorem rsL2Norm_nonneg (α : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℂ) :
    0 ≤ rsL2Norm α a b f := Real.sqrt_nonneg _

/-- Schwarz for the real product of the two pointwise norms. Zero norms are allowed. -/
theorem schwarz_norm_values {a b A B C : ℝ} {f g : ℝ → ℂ} {α : ℝ → ℝ}
    (hA : HasRSIntegral (fun x => ‖f x‖ ^ 2) α a b A)
    (hB : HasRSIntegral (fun x => ‖g x‖ ^ 2) α a b B)
    (hC : HasRSIntegral (fun x => ‖f x‖ * ‖g x‖) α a b C) :
    C ≤ Real.sqrt A * Real.sqrt B := by
  have h := holder_real_values Real.HolderConjugate.two_two
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    (by simpa only [Real.rpow_two] using hA)
    (by simpa only [Real.rpow_two] using hB) hC
  simpa only [Real.sqrt_eq_rpow] using h

/-- The additive triangle bound follows from Schwarz and the squared norm bound. -/
theorem rsL2Norm_add_le {a b : ℝ} {f g : ℝ → ℂ} {α : ℝ → ℝ} {v w : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b v)
    (hg : HasComplexRSIntegral g α a b w) :
    rsL2Norm α a b (fun x => f x + g x) ≤ rsL2Norm α a b f + rsL2Norm α a b g := by
  obtain ⟨A, hA⟩ := exists_l2_integral hab hf
  obtain ⟨B, hB⟩ := exists_l2_integral hab hg
  obtain ⟨E, hE⟩ := exists_l2_integral hab (hasComplexRSIntegral_add hf hg)
  obtain ⟨F, hF⟩ := exists_norm hab hf
  obtain ⟨G, hG⟩ := exists_norm hab hg
  obtain ⟨C, hC⟩ := exists_tagged_product hab hF hG
  have hSchwarz := schwarz_norm_values hA hB hC
  have hbound := hasRSIntegral_mono hE
    (hasRSIntegral_add (hasRSIntegral_add hA (hasRSIntegral_mul hC 2)) hB)
    (fun x _ => by
      have h := norm_add_le (f x) (g x)
      have hf₀ := norm_nonneg (f x)
      have hg₀ := norm_nonneg (g x)
      have hs₀ := norm_nonneg (f x + g x)
      nlinarith)
  have hA₀ := hasRSIntegral_nonneg hA (fun _ _ => sq_nonneg _)
  have hB₀ := hasRSIntegral_nonneg hB (fun _ _ => sq_nonneg _)
  have hE₀ := hasRSIntegral_nonneg hE (fun _ _ => sq_nonneg _)
  rw [rsL2Norm_eq hE, rsL2Norm_eq hA, rsL2Norm_eq hB]
  have hsA := Real.sq_sqrt hA₀
  have hsB := Real.sq_sqrt hB₀
  have hsE := Real.sq_sqrt hE₀
  have hnA := Real.sqrt_nonneg A
  have hnB := Real.sqrt_nonneg B
  have hnE := Real.sqrt_nonneg E
  nlinarith

/-- Exercise 11: the required triangle inequality is for three differences.
No assertion that this seminorm separates functions is used or implied. -/
theorem rsL2Norm_difference_triangle {a b : ℝ} {f g h : ℝ → ℂ}
    {α : ℝ → ℝ} {u v w : ℂ} (hab : a ≤ b)
    (hf : HasComplexRSIntegral f α a b u) (hg : HasComplexRSIntegral g α a b v)
    (hh : HasComplexRSIntegral h α a b w) :
    rsL2Norm α a b (fun x => f x - h x) ≤
      rsL2Norm α a b (fun x => f x - g x) + rsL2Norm α a b (fun x => g x - h x) := by
  have heq : (fun x => (f x - g x) + (g x - h x)) = (fun x => f x - h x) := by
    funext x
    ring
  simpa only [heq] using rsL2Norm_add_le hab
    (hasComplexRSIntegral_sub hf hg) (hasComplexRSIntegral_sub hg hh)

/-- The real embedding preserves the literal tagged integral. -/
theorem hasComplexRSIntegral_real {a b v : ℝ} {f α : ℝ → ℝ}
    (hf : HasRSIntegral f α a b v) :
    HasComplexRSIntegral (fun x => (f x : ℂ)) α a b (v : ℂ) := by
  apply hasComplexRSIntegral_iff.mpr
  constructor
  · simpa only [Complex.ofReal_re] using hf
  · simpa only [Complex.ofReal_im, zero_mul] using hasRSIntegral_mul hf 0

/-- The source triangle inequality also applies directly to three real
raw-integrable functions, with the same L² seminorm under the real embedding. -/
theorem rsL2Norm_real_difference_triangle {a b u v w : ℝ} {f g h α : ℝ → ℝ}
    (hab : a ≤ b) (hf : HasRSIntegral f α a b u) (hg : HasRSIntegral g α a b v)
    (hh : HasRSIntegral h α a b w) :
    rsL2Norm α a b (fun x => ((f x - h x : ℝ) : ℂ)) ≤
      rsL2Norm α a b (fun x => ((f x - g x : ℝ) : ℂ)) +
      rsL2Norm α a b (fun x => ((g x - h x : ℝ) : ℂ)) := by
  simpa only [Complex.ofReal_sub] using rsL2Norm_difference_triangle hab
    (hasComplexRSIntegral_real hf) (hasComplexRSIntegral_real hg) (hasComplexRSIntegral_real hh)

/-- A zero integrator gives zero seminorm even for the constant function one. -/
theorem rsL2Norm_constant_one_zero_integrator {a b : ℝ} (hab : a ≤ b) :
    rsL2Norm (fun _ => 0) a b (fun _ => (1 : ℂ)) = 0 := by
  apply (rsL2Norm_eq (show HasRSIntegral (fun _ => ‖(1 : ℂ)‖ ^ 2)
    (fun _ => 0) a b 0 from ?_)).trans (Real.sqrt_zero)
  simpa using hasRSIntegral_constant hab (monotone_const.monotoneOn _) (1 : ℝ)

end Rudin.Chapter06
