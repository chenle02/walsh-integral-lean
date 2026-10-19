import Mathlib

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace WalshIntegral.WhiteNoise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Standard Gaussian coordinates are orthonormal as elements of the real L2 space. -/
theorem orthonormal_gaussianLp (ξ : ℕ → Lp ℝ 2 P)
    (hlaw : ∀ n, HasLaw (fun ω => ξ n ω) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun n ω => ξ n ω) P) : Orthonormal ℝ ξ := by
  have hmean (n : ℕ) : ∫ ω, ξ n ω ∂P = 0 := by
    simpa using (hlaw n).integral_eq
  have hcov (i j : ℕ) :
      covariance (fun ω => ξ i ω) (fun ω => ξ j ω) P = inner ℝ (ξ i) (ξ j) := by
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hmean i, hmean j]
    simp only [zero_mul, sub_zero, L2.inner_def, RCLike.inner_apply,
      conj_trivial, Pi.mul_apply, mul_comm]
  rw [orthonormal_iff_ite]
  intro i j
  rw [← hcov]
  split_ifs with hij
  · subst j
    rw [covariance_self (Lp.stronglyMeasurable (ξ i)).aemeasurable]
    simpa using (hlaw i).variance_eq
  · exact (hind.indepFun hij).covariance_eq_zero (Lp.memLp _) (Lp.memLp _)

/-- The isometric series map associated with an orthonormal sequence. -/
def orthonormalSeries {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (ξ : ℕ → E) (hξ : Orthonormal ℝ ξ) :
    lp (fun _ : ℕ => ℝ) 2 →ₗᵢ[ℝ] E :=
  hξ.orthogonalFamily.linearIsometry

/-- Initial partial sums converge in norm to the orthonormal series map. -/
theorem orthonormalSeries_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (ξ : ℕ → E) (hξ : Orthonormal ℝ ξ)
    (c : lp (fun _ : ℕ => ℝ) 2) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, c n • ξ n) atTop
      (𝓝 (orthonormalSeries ξ hξ c)) := by
  exact hξ.orthogonalFamily.hasSum_linearIsometry c |>.tendsto_sum_nat

omit [IsProbabilityMeasure P] in
/-- The Gaussian law of a centered L2 class is determined by its norm. -/
theorem gaussianLp_law (f : Lp ℝ 2 P)
    (hg : HasGaussianLaw (fun ω => f ω) P) (hm : ∫ ω, f ω ∂P = 0) :
    P.map (fun ω => f ω) = gaussianReal 0 (‖f‖₊ ^ 2) := by
  rw [hg.map_eq_gaussianReal, hm]
  congr 1
  have hv : variance (fun ω => f ω) P = ‖f‖ ^ 2 := by
    rw [variance_of_integral_eq_zero hg.aemeasurable hm]
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, pow_two] using
      (real_inner_self_eq_norm_sq f)
  rw [hv]
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

/-- Centered Gaussian laws with the L2 norm as standard deviation pass to L2 limits. -/
theorem gaussian_law_of_tendsto_Lp (f : ℕ → Lp ℝ 2 P) (g : Lp ℝ 2 P)
    (hlim : Tendsto f atTop (𝓝 g))
    (hlaw : ∀ n, P.map (fun ω => f n ω) = gaussianReal 0 (‖f n‖₊ ^ 2)) :
    P.map (fun ω => g ω) = gaussianReal 0 (‖g‖₊ ^ 2) := by
  apply Measure.ext_of_charFun
  funext t
  have hd := (tendstoInMeasure_of_tendsto_Lp hlim).tendstoInDistribution
    (fun n => (Lp.stronglyMeasurable (f n)).aemeasurable)
  have hc := hd.tendsto_charFun t
  simp_rw [hlaw, charFun_gaussianReal] at hc
  rw [charFun_gaussianReal]
  apply tendsto_nhds_unique hc
  have hnorm := hlim.norm
  simp only [NNReal.coe_pow, coe_nnnorm]
  exact (by fun_prop : Continuous (fun r : ℝ =>
    Complex.exp (↑t * ↑(0 : ℝ) * Complex.I - ↑(r ^ 2) * ↑t ^ 2 / 2))).continuousAt.tendsto.comp hnorm

/-- Finite linear combinations of independent standard Gaussian L2 classes are Gaussian. -/
theorem gaussianLp_sum_law (ξ : ℕ → Lp ℝ 2 P)
    (hlaw : ∀ n, HasLaw (fun ω => ξ n ω) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun n ω => ξ n ω) P) (c : ℕ → ℝ) (I : Finset ℕ) :
    P.map (fun ω => (∑ n ∈ I, c n • ξ n : Lp ℝ 2 P) ω) =
      gaussianReal 0 (‖∑ n ∈ I, c n • ξ n‖₊ ^ 2) := by
  have hae : (fun ω => (∑ n ∈ I, c n • ξ n : Lp ℝ 2 P) ω) =ᵐ[P]
      (fun ω => ∑ n : I, c n * ξ n ω) := by
    filter_upwards [Lp.coeFn_finsetSum I (fun n => c n • ξ n),
      ae_all_iff.mpr (fun n => Lp.coeFn_smul (c n) (ξ n))] with ω hsum hsmul
    simp only [Finset.sum_apply] at hsum
    rw [hsum, Finset.sum_coe_sort I (fun n => c n * ξ n ω)]
    exact Finset.sum_congr rfl fun n _ => hsmul n
  have hg (n : ℕ) : HasGaussianLaw (fun ω => ξ n ω) P := by
    refine ⟨(hlaw n).aemeasurable, ?_⟩
    rw [(hlaw n).map_eq]
    infer_instance
  have hgs : HasGaussianLaw (fun ω => ∑ n : I, c n * ξ n ω) P := by
    have hi := (hind.restrict I).comp (fun n : I => fun x : ℝ => c n * x)
      (fun _ => by fun_prop)
    exact hi.hasGaussianLaw_fun_sum (fun n => (hg n).fun_smul (c n))
  apply gaussianLp_law
  · exact hgs.congr hae.symm
  · rw [integral_congr_ae hae, integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro n _
      rw [integral_const_mul]
      have hm : ∫ ω, ξ n ω ∂P = 0 := by simpa using (hlaw n).integral_eq
      rw [hm, mul_zero]
    · intro n _
      exact ((Lp.memLp (ξ n)).integrable (by norm_num)).const_mul _

/-- A square-summable independent Gaussian series has the Gaussian law with its L2 variance. -/
theorem orthonormalSeries_gaussian_law (ξ : ℕ → Lp ℝ 2 P)
    (hlaw : ∀ n, HasLaw (fun ω => ξ n ω) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun n ω => ξ n ω) P) (c : lp (fun _ : ℕ => ℝ) 2) :
    P.map (fun ω => orthonormalSeries ξ (orthonormal_gaussianLp ξ hlaw hind) c ω) =
      gaussianReal 0 (‖c‖₊ ^ 2) := by
  have hlim := orthonormalSeries_tendsto ξ (orthonormal_gaussianLp ξ hlaw hind) c
  have hg := gaussian_law_of_tendsto_Lp _ _ hlim
    (fun N => gaussianLp_sum_law ξ hlaw hind c (Finset.range N))
  simpa only [LinearIsometry.nnnorm_map] using hg

omit [IsProbabilityMeasure P] in
/-- Finite evaluation of a linear map into L2 commutes with linear combinations almost surely. -/
theorem linearLp_sum_ae {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (W : D →L[ℝ] Lp ℝ 2 P) {ι : Type*} [Fintype ι] (h : ι → D) (a : ι → ℝ) :
    (fun ω => W (∑ i, a i • h i) ω) =ᵐ[P] (fun ω => ∑ i, a i * W (h i) ω) := by
  simp only [map_sum, map_smul]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => a i • W (h i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (W (h i)))] with ω hsum hsmul
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ => hsmul i

omit [IsProbabilityMeasure P] in
/-- A linear L2 family with Gaussian marginals is a Gaussian process. -/
theorem linearLp_isGaussianProcess {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (W : D →L[ℝ] Lp ℝ 2 P) (hg : ∀ h, HasGaussianLaw (fun ω => W h ω) P) :
    IsGaussianProcess (fun h ω => W h ω) P := by
  classical
  constructor
  intro I
  refine ⟨(measurable_pi_iff.mpr fun i : I =>
      (Lp.stronglyMeasurable (W i)).measurable).aemeasurable,
    isGaussian_of_isGaussian_map fun L => ?_⟩
  let a : I → ℝ := fun i => L (fun j => if i = j then 1 else 0)
  have hae : (fun ω => L (fun i : I => W i ω)) =ᵐ[P]
      (fun ω => W (∑ i : I, a i • (i : D)) ω) := by
    refine EventuallyEq.trans ?_ ((linearLp_sum_ae W (fun i : I => (i : D)) a).symm)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [a, smul_eq_mul, mul_comm, ContinuousLinearMap.coe_coe] using
        L.toLinearMap.pi_apply_eq_sum_univ (fun i : I => W i ω)
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact ((hg _).congr hae.symm).isGaussian_map

/-- A separable real Hilbert space containing an infinite orthonormal sequence has a countable basis. -/
theorem exists_nat_hilbertBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (v : ℕ → E) (hv : Orthonormal ℝ v) : Nonempty (HilbertBasis ℕ ℝ E) := by
  classical
  obtain ⟨w, b, hw, hb⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  have : Infinite w := (Set.Infinite.mono hw
    (Set.infinite_range_of_injective hv.linearIndependent.injective)).to_subtype
  have hd : Pairwise (fun i j : w => Disjoint (Metric.ball (b i) (1 / 2 : ℝ))
      (Metric.ball (b j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have heq := norm_sub_sq_real (b i) (b j)
    rw [b.orthonormal.norm_eq_one i, b.orthonormal.norm_eq_one j,
      b.orthonormal.inner_eq_zero hij] at heq
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (b i - b j)]
  have : Countable w := hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  let e : ℕ ≃ w := Classical.choice nonempty_equiv_of_countable
  refine ⟨HilbertBasis.mk (b.orthonormal.comp e e.injective) ?_⟩
  rw [Set.range_comp, e.surjective.range_eq, Set.image_univ, b.dense_span]

end WalshIntegral.WhiteNoise
