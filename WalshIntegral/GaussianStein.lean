import Mathlib

/-!
# One-dimensional Gaussian integration by parts (Stein's identity).

For the centred Gaussian law `N(0, v)` on `ℝ` (Mathlib's `ProbabilityTheory.gaussianReal 0 v`,
which is the Dirac mass at `0` when `v = 0`) and a differentiable `g` with derivative `g'`,

  `∫ y * g y ∂N(0, v) = v * ∫ g' y ∂N(0, v)`.

The main statement `integral_mul_eq_variance_mul_integral_deriv` assumes polynomial growth of
`g` and `g'`; the general form `integral_mul_eq_variance_mul_integral_deriv_of_integrable` only
asks that `g`, `g'` and `y ↦ y * g y` be integrable for the Gaussian law. The case `v = 0` is the
Dirac case, where both sides vanish.

The proof for `v ≠ 0` is integration by parts on `ℝ` against the density, using
`hasDerivAt_gaussianPDFReal`: the density `φ` of `N(μ, v)` satisfies `φ' x = -((x - μ) / v) φ x`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace WalshIntegral.GaussianStein

/-- The derivative of the Gaussian density: `φ' x = -((x - μ) / v) * φ x`. For `v = 0` the
density is the zero function and both sides are `0`. -/
theorem hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h0 : HasDerivAt (fun y : ℝ => (y - μ) ^ 2) (2 * (x - μ)) x := by
    simpa using ((hasDerivAt_id' x).sub_const μ).fun_pow 2
  have h1 : HasDerivAt (fun y : ℝ => -(y - μ) ^ 2 / (2 * (v : ℝ))) (-((x - μ) / v)) x := by
    convert h0.const_mul (-(2 * (v : ℝ))⁻¹) using 1
    · funext y
      ring
    · field_simp
  have h := h1.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  rw [gaussianPDFReal_def]
  convert h using 1
  ring

/-- `(1 + |y|) ^ n` is integrable for every Gaussian law on `ℝ`. -/
theorem integrable_one_add_abs_pow (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ n) (gaussianReal μ v) := by
  have hsum : Integrable (fun y : ℝ => Real.exp (n * y) + Real.exp (-(n : ℝ) * y))
      (gaussianReal μ v) :=
    (integrable_exp_mul_gaussianReal (n : ℝ)).add (integrable_exp_mul_gaussianReal (-(n : ℝ)))
  refine hsum.mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  have h0 : 0 ≤ 1 + |y| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 n)]
  have h1 : (1 + |y|) ^ n ≤ Real.exp (n * |y|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp |y|]) n
  have h2 : Real.exp (n * |y|) ≤ Real.exp (n * y) + Real.exp (-(n : ℝ) * y) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      linarith [Real.exp_pos (-(n : ℝ) * y)]
    · rw [abs_of_nonpos hy, mul_neg, ← neg_mul]
      linarith [Real.exp_pos ((n : ℝ) * y)]
  exact h1.trans h2

/-- Integrability for a Gaussian law with `v ≠ 0` transfers to integrability of the product with
the density for Lebesgue measure. -/
theorem integrable_pdf_mul_of_integrable {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal μ v)) :
    Integrable (fun x => gaussianPDFReal μ v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using hf

/-- One-dimensional Gaussian integration by parts, assuming only integrability of `g`, `g'` and
`y ↦ y * g y` for the Gaussian law. Includes the Dirac case `v = 0`. -/
theorem integral_mul_eq_variance_mul_integral_deriv_of_integrable (v : ℝ≥0) {g g' : ℝ → ℝ}
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hig : Integrable g (gaussianReal 0 v)) (hig' : Integrable g' (gaussianReal 0 v))
    (hyg : Integrable (fun y => y * g y) (gaussianReal 0 v)) :
    ∫ y, y * g y ∂(gaussianReal 0 v) = (v : ℝ) * ∫ y, g' y ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  set φ : ℝ → ℝ := gaussianPDFReal 0 v with hφ
  set φ' : ℝ → ℝ := fun x => -((x - 0) / v) * φ x with hφ'
  have hderiv : ∀ x, HasDerivAt φ (φ' x) x := hasDerivAt_gaussianPDFReal 0 v
  have i1 : Integrable (fun x => φ x * g x) := integrable_pdf_mul_of_integrable hv hig
  have i2 : Integrable (fun x => φ x * g' x) := integrable_pdf_mul_of_integrable hv hig'
  have i3 : Integrable (fun x => φ x * (x * g x)) := integrable_pdf_mul_of_integrable hv hyg
  have huv' : Integrable (g * φ') :=
    (i3.const_mul (-(v : ℝ)⁻¹)).congr (ae_of_all _ fun x => by
      simp only [hφ', Pi.mul_apply, sub_zero]
      ring)
  have hu'v : Integrable (g' * φ) := i2.congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      ring)
  have huv : Integrable (g * φ) := i1.congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      ring)
  have hibp : ∫ x, g x * φ' x = -∫ x, g' x * φ x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hg x) (fun x _ => hderiv x)
      huv' hu'v huv
  have key : ∀ x, φ x * (x * g x) = -(v : ℝ) * (g x * φ' x) := by
    intro x
    simp only [hφ', sub_zero]
    field_simp
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  calc
    ∫ x, φ x * (x * g x) = ∫ x, -(v : ℝ) * (g x * φ' x) := by
      congr 1
      funext x
      exact key x
    _ = -(v : ℝ) * ∫ x, g x * φ' x := integral_const_mul _ _
    _ = (v : ℝ) * ∫ x, g' x * φ x := by
      rw [hibp, neg_mul_neg]
    _ = (v : ℝ) * ∫ x, φ x * g' x := by
      congr 1
      congr 1
      funext x
      ring

/-- One-dimensional Gaussian integration by parts (Stein's identity). -/
theorem integral_mul_eq_variance_mul_integral_deriv (v : ℝ≥0) {g g' : ℝ → ℝ}
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : Continuous g')
    (hpoly : ∃ C : ℝ, ∃ n : ℕ, ∀ y, |g y| ≤ C * (1 + |y|) ^ n ∧ |g' y| ≤ C * (1 + |y|) ^ n) :
    ∫ y, y * g y ∂(ProbabilityTheory.gaussianReal 0 v) =
      (v : ℝ) * ∫ y, g' y ∂(ProbabilityTheory.gaussianReal 0 v) := by
  obtain ⟨C, n, hC⟩ := hpoly
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun y => (hg y).continuousAt
  have hig : Integrable g (gaussianReal 0 v) :=
    ((integrable_one_add_abs_pow 0 v n).const_mul C).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using (hC y).1)
  have hig' : Integrable g' (gaussianReal 0 v) :=
    ((integrable_one_add_abs_pow 0 v n).const_mul C).mono' hg'.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using (hC y).2)
  have hyg : Integrable (fun y => y * g y) (gaussianReal 0 v) := by
    refine ((integrable_one_add_abs_pow 0 v (n + 1)).const_mul C).mono'
      (continuous_id.mul hgc).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    have h0 : 0 ≤ 1 + |y| := by positivity
    have hgy : |g y| ≤ C * (1 + |y|) ^ n := (hC y).1
    rw [Real.norm_eq_abs, abs_mul, pow_succ]
    calc
      |y| * |g y| ≤ (1 + |y|) * |g y| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (1 + |y|) * (C * (1 + |y|) ^ n) := mul_le_mul_of_nonneg_left hgy h0
      _ = C * ((1 + |y|) ^ n * (1 + |y|)) := by ring
  exact integral_mul_eq_variance_mul_integral_deriv_of_integrable v hg hig hig' hyg

end WalshIntegral.GaussianStein
