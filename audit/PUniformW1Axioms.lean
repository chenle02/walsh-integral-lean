import WalshIntegral.GaussianStein
import WalshIntegral.MomentBound

#print axioms WalshIntegral.GaussianStein.hasDerivAt_gaussianPDFReal
#print axioms WalshIntegral.GaussianStein.integrable_one_add_abs_pow
#print axioms WalshIntegral.GaussianStein.integrable_pdf_mul_of_integrable
#print axioms WalshIntegral.GaussianStein.integral_mul_eq_variance_mul_integral_deriv_of_integrable
#print axioms WalshIntegral.GaussianStein.integral_mul_eq_variance_mul_integral_deriv

/-- Interface check: the frozen O1 signature, restated verbatim. -/
example (v : NNReal) {g g' : ℝ → ℝ}
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : Continuous g')
    (hpoly : ∃ C : ℝ, ∃ n : ℕ, ∀ y, |g y| ≤ C * (1 + |y|) ^ n ∧ |g' y| ≤ C * (1 + |y|) ^ n) :
    ∫ y, y * g y ∂(ProbabilityTheory.gaussianReal 0 v) =
      (v : ℝ) * ∫ y, g' y ∂(ProbabilityTheory.gaussianReal 0 v) :=
  WalshIntegral.GaussianStein.integral_mul_eq_variance_mul_integral_deriv v hg hg' hpoly

-- O3: sharp linear constant.
#print axioms WalshIntegral.MomentBound.bdgConst_eq
#print axioms WalshIntegral.MomentBound.bdgConst_le_self
#print axioms WalshIntegral.MomentBound.bdgConst_nonneg
#print axioms WalshIntegral.MomentBound.eLpNorm_slabVariance_le
#print axioms WalshIntegral.MomentBound.eLpNorm_slab_sq_le
#print axioms WalshIntegral.MomentBound.eLpNorm_add_slab_sq_le
#print axioms WalshIntegral.MomentBound.eLpNorm_elementarySumIntegral_sq_le
#print axioms WalshIntegral.MomentBound.eLpNorm_walshT_sq_le
#print axioms WalshIntegral.GaussianStep.slab_gram_eq
#print axioms WalshIntegral.GaussianStep.eLpNorm_add_gaussian_slab_sq_le
