module

public import Challenge.Reference.WalshIntegral.IntegralIncrements

public import Challenge.Reference.WalshIntegral.WhiteNoise
public import Challenge.Reference.WalshIntegral.Predictable
public import Challenge.Reference.WalshIntegral.Integral
public import Challenge.Reference.WalshIntegral.MomentBound

@[expose] public section
/-!
# Predictable modifications on the full finite-variance domain for regular causal kernels. Equality holds almost surely separately at each output point; sample continuity and a common exceptional set are not asserted.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace WalshIntegral.Modification

open WalshIntegral.WhiteNoise WalshIntegral.Predictable WalshIntegral.Integral

/-- Deterministic causal kernels with exactly the L² regularity used by the corresponding interface.
Input integration uses positive-time Lebesgue measure times spatial Lebesgue
measure. The continuity condition includes all nonpositive output times. -/
structure CausalKernel where
  K : ℝ → ℝ → ℝ → ℝ → ℝ
  measurable : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
    K q.1.1 q.1.2 q.2.1 q.2.2)
  causal : ∀ t x s y, s ≤ 0 ∨ t ≤ s → K t x s y = 0
  memLp : ∀ t x, MemLp (fun z : ℝ × ℝ => K t x z.1 z.2) 2 timeSpaceVolume
  tendsto_sq : ∀ z : ℝ × ℝ,
    Tendsto (fun z' : ℝ × ℝ => ∫⁻ w : ℝ × ℝ,
      ENNReal.ofReal ((K z'.1 z'.2 w.1 w.2 - K z.1 z.2 w.1 w.2) ^ 2)
        ∂timeSpaceVolume) (𝓝 z) (𝓝 0)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Multiply the input field by the kernel at a fixed output point. -/
def kernelField (K : CausalKernel) (t x : ℝ) (Φ : ℝ → ℝ → Ω → ℝ) :
    ℝ → ℝ → Ω → ℝ :=
  fun s y ω => K.K t x s y * Φ s y ω

/-- Amplitude clipping only, with no time or spatial localization. -/
def clipField (n : ℕ) (Φ : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ :=
  fun s y ω => max (-(n : ℝ)) (min (n : ℝ) (Φ s y ω))

/-- The kernel-weighted squared sample L² norm, in a deterministic weighted-norm form.
For a cut-off heat kernel, Tonelli identifies this with the corresponding variance integral. -/
def kernelVariance (P : Measure Ω) (K : CausalKernel)
    (Φ : ℝ → ℝ → Ω → ℝ) (t x : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (K.K t x z.1 z.2 ^ 2) *
    eLpNorm (Φ z.1 z.2) 2 P ^ 2 ∂timeSpaceVolume

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- Clipping preserves predictability on the entire real-time domain. -/
theorem clipField_measurable (n : ℕ) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => clipField n Φ q.1 q.2.1 q.2.2) := by
  exact measurable_const.max (measurable_const.min hΦ)

set_option linter.unusedSectionVars false in
/-- The clipped field is bounded by its natural-number clipping level. -/
theorem clipField_abs_le (n : ℕ) (Φ : ℝ → ℝ → Ω → ℝ) (s y : ℝ) (ω : Ω) :
    |clipField n Φ s y ω| ≤ (n : ℝ) := by
  rw [clipField, abs_le]
  exact ⟨le_max_left _ _, max_le (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (min_le_left _ _)⟩

/-- A deterministic Borel kernel section preserves input predictability. -/
theorem kernelField_measurable (K : CausalKernel) (t x : ℝ)
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => kernelField K t x Φ q.1 q.2.1 q.2.2) := by
  exact (K.measurable.comp
    ((measurable_const (a := (t, x))).prodMk (measurable_coord F))).mul hΦ

variable [IsProbabilityMeasure P]

set_option linter.unusedSectionVars false in
private theorem sample_sq_lintegral (f : Ω → ℝ) (hf : Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P) = eLpNorm f 2 P ^ 2 := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      hf.aestronglyMeasurable (μ := P)).symm

private theorem kernelVariance_eq_lintegral (K : CausalKernel) (t x : ℝ)
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    kernelVariance P K Φ t x =
      ∫⁻ q : ℝ × ℝ × Ω, ENNReal.ofReal (kernelField K t x Φ q.1 q.2.1 q.2.2 ^ 2)
        ∂spaceTimeSample P := by
  have hm := (kernelField_measurable K t x Φ hΦ).mono (predictableSigma_le F) le_rfl
  have hm' : Measurable (fun q : (ℝ × ℝ) × Ω =>
      kernelField K t x Φ q.1.1 q.1.2 q.2) := hm.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  rw [spaceTimeSample_eq_map, lintegral_map (hm.pow_const 2).ennreal_ofReal
    MeasurableEquiv.prodAssoc.measurable]
  change _ = ∫⁻ q : (ℝ × ℝ) × Ω,
    ENNReal.ofReal (kernelField K t x Φ q.1.1 q.1.2 q.2 ^ 2) ∂timeSpaceVolume.prod P
  rw [lintegral_prod _ (hm'.pow_const 2).ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro z
  rw [sample_sq_lintegral (kernelField K t x Φ z.1 z.2)
    (hm'.comp ((measurable_const (a := z)).prodMk measurable_id))]
  change _ = eLpNorm (K.K t x z.1 z.2 • Φ z.1 z.2) 2 P ^ 2
  rw [eLpNorm_const_smul, mul_pow, ← ofReal_norm, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- On predictable inputs, finite kernel variance is exactly the integral domain.
This prevents any appeal to off-domain zero totalization in the main result. -/
theorem kernelField_inDomain_iff (K : CausalKernel) (t x : ℝ)
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    InDomain F P (kernelField K t x Φ) ↔ kernelVariance P K Φ t x < ⊤ := by
  rw [kernelVariance_eq_lintegral K t x Φ hΦ]
  exact and_iff_right (kernelField_measurable K t x Φ hΦ)

/-- Every bounded truncation lies in the integration domain at every output point. -/
theorem kernelField_clipField_inDomain (K : CausalKernel) (n : ℕ)
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) (t x : ℝ) :
    InDomain F P (kernelField K t x (clipField n Φ)) := by
  apply (kernelField_inDomain_iff K t x _ (clipField_measurable n Φ hΦ)).mpr
  have hm := (clipField_measurable n Φ hΦ).mono (predictableSigma_le F) le_rfl
  have hb (z : ℝ × ℝ) : eLpNorm (clipField n Φ z.1 z.2) 2 P ≤ ENNReal.ofReal n := by
    have hs : Measurable (clipField n Φ z.1 z.2) :=
      hm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using eLpNorm_le_of_ae_bound (p := 2) (μ := P) hs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using clipField_abs_le n Φ z.1 z.2 ω)
  have hK : (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (K.K t x z.1 z.2 ^ 2)
      ∂timeSpaceVolume) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp
      (K.memLp t x).integrable_sq.2
  calc
    kernelVariance P K (clipField n Φ) t x ≤
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (K.K t x z.1 z.2 ^ 2) *
          ENNReal.ofReal (n : ℝ) ^ 2 ∂timeSpaceVolume := by
      apply lintegral_mono
      intro z
      exact mul_le_mul le_rfl (pow_le_pow_left' (hb z) 2) bot_le bot_le
    _ = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (K.K t x z.1 z.2 ^ 2) ∂timeSpaceVolume) *
        ENNReal.ofReal (n : ℝ) ^ 2 := by
      exact lintegral_mul_const _
        ((K.measurable.comp ((measurable_const (a := (t, x))).prodMk measurable_id)).pow_const 2).ennreal_ofReal
    _ < ⊤ := ENNReal.mul_lt_top hK (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

variable {W : H →L[ℝ] Lp ℝ 2 P}

set_option linter.unusedSectionVars false in
private theorem exists_restrictPredL2 (t : ℝ) :
    ∃ R : PredL2 F P →L[ℝ] PredL2 F P, ∀ f : PredL2 F P,
      (fun q => (R f).val q) =ᵐ[spaceTimeSample P]
        {q : ℝ × ℝ × Ω | q.1 ∈ Set.Ioc 0 t}.indicator (fun q => f.val q) := by
  classical
  let S : Set (ℝ × ℝ × Ω) := {q | q.1 ∈ Set.Ioc 0 t}
  have hS : MeasurableSet[predictableSigma F] S :=
    measurableSet_Ioc.preimage (measurable_coord F).fst
  have hSa : NullMeasurableSet S (spaceTimeSample P) :=
    (predictableSigma_le F _ hS).nullMeasurableSet
  let R (f : PredL2 F P) : PredL2 F P :=
    ⟨((Lp.memLp f.val).indicator hSa).toLp (S.indicator (fun q => f.val q)),
      by
        obtain ⟨g, hg, hfg⟩ := lpMeas.aestronglyMeasurable f
        exact ⟨S.indicator g, hg.indicator hS,
          ((Lp.memLp f.val).indicator hSa).coeFn_toLp.trans hfg.indicator⟩⟩
  have hR (f : PredL2 F P) : (fun q => (R f).val q) =ᵐ[spaceTimeSample P]
      S.indicator (fun q => f.val q) := ((Lp.memLp f.val).indicator hSa).coeFn_toLp
  let L : PredL2 F P →ₗ[ℝ] PredL2 F P :=
    { toFun := R
      map_add' := by
        intro f g
        apply Subtype.ext
        apply Lp.ext
        filter_upwards [hR (f + g), hR f, hR g, Lp.coeFn_add f.val g.val,
          Lp.coeFn_add (R f).val (R g).val] with q hfg hf hg hadd hout
        change (R (f + g)).val q = ((R f).val + (R g).val) q
        simp only [hfg, hout, Pi.add_apply, hf, hg]
        by_cases hq : q ∈ S
        · simpa only [Set.indicator_of_mem hq, Submodule.coe_add, Pi.add_apply] using hadd
        · simp only [Set.indicator_of_notMem hq, add_zero]
      map_smul' := by
        intro c f
        apply Subtype.ext
        apply Lp.ext
        filter_upwards [hR (c • f), hR f, Lp.coeFn_smul c f.val,
          Lp.coeFn_smul c (R f).val] with q hcf hf hsmul hout
        change (R (c • f)).val q = (c • (R f).val) q
        simp only [hcf, hout, Pi.smul_apply, hf]
        by_cases hq : q ∈ S <;> simp [hq, hsmul] }
  have hbound (f : PredL2 F P) : ‖L f‖ ≤ 1 * ‖f‖ := by
    change ‖((Lp.memLp f.val).indicator hSa).toLp _‖ ≤ 1 * ‖f.val‖
    rw [Lp.norm_toLp, one_mul, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f.val).eLpNorm_ne_top
      (eLpNorm_indicator_le _ hSa)
  exact ⟨L.mkContinuous 1 hbound, hR⟩

private theorem restricted_elementary_adapted (hW : IsWhiteNoise P F W) (t : ℝ≥0)
    (R : PredL2 F P →L[ℝ] PredL2 F P)
    (hR : ∀ f : PredL2 F P, (fun q => (R f).val q) =ᵐ[spaceTimeSample P]
      {q : ℝ × ℝ × Ω | q.1 ∈ Set.Ioc 0 (t : ℝ)}.indicator (fun q => f.val q))
    (e : Elementary F) :
    walshL2 hW (R (elementaryClass P e)) ∈ lpMeas ℝ ℝ (F t) 2 P := by
  classical
  let S : Set (ℝ × ℝ × Ω) := {q | q.1 ∈ Set.Ioc 0 (t : ℝ)}
  by_cases hst : e.s < t
  · let d : Elementary F := { e with t := min e.t t, s_lt_t := lt_min e.s_lt_t hst }
    have hfield (q : ℝ × ℝ × Ω) :
        S.indicator (fun q => e.field q.1 q.2.1 q.2.2) q = d.field q.1 q.2.1 q.2.2 := by
      simp only [S, Elementary.field, d, NNReal.coe_min, Set.indicator_apply,
        Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioc, le_min_iff]
      have hs := e.s.coe_nonneg
      split_ifs <;> simp_all only [mul_one, mul_zero] <;> grind
    have heq : R (elementaryClass P e) = elementaryClass P d := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hR (elementaryClass P e), toPredL2_ae e.field e.inDomain,
        toPredL2_ae d.field d.inDomain] with q hr he hd
      change (R (elementaryClass P e)).val q = (toPredL2 d.field d.inDomain).val q
      rw [hr, hd, ← hfield]
      change S.indicator (fun q => (elementaryClass P e).val q) q =
        S.indicator (fun q => e.field q.1 q.2.1 q.2.2) q
      by_cases hq : q ∈ S
      · simpa only [Set.indicator_of_mem hq, elementaryClass] using he
      · simp only [Set.indicator_of_notMem hq]
    rw [heq, walshL2_elementary]
    have hsupp : SupportedBefore t
        (rectangle d.s d.t d.A d.measurableSet_A d.volume_A_ne_top) := by
      filter_upwards [rectangle_supportedBefore d.s d.t d.A d.measurableSet_A
        d.volume_A_ne_top] with z hz htz
      exact hz (lt_of_le_of_lt (by exact_mod_cast min_le_right e.t t) htz)
    obtain ⟨X, hXm, hXa⟩ := hW.adapted t _ hsupp
    refine ⟨fun ω => d.coeff ω * X ω,
      ((d.measurable_coeff.mono (F.mono hst.le) le_rfl).mul hXm.measurable).stronglyMeasurable, ?_⟩
    filter_upwards [elementaryIntegral_ae W d, hXa] with ω he hx
    rw [he, hx]
  · have hfield (q : ℝ × ℝ × Ω) :
        S.indicator (fun q => e.field q.1 q.2.1 q.2.2) q = 0 := by
      have hts : (t : ℝ) ≤ e.s := by exact_mod_cast le_of_not_gt hst
      simp only [S, Elementary.field, Set.indicator_apply,
        Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioc]
      split_ifs <;> simp_all only [mul_one, mul_zero]
      grind
    have heq : R (elementaryClass P e) = 0 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hR (elementaryClass P e), toPredL2_ae e.field e.inDomain,
        Lp.coeFn_zero ℝ 2 (spaceTimeSample P)] with q hr he hz
      change (R (elementaryClass P e)).val q = (0 : Lp ℝ 2 (spaceTimeSample P)) q
      rw [hr, hz]
      change S.indicator (fun q => (elementaryClass P e).val q) q = 0
      rw [← hfield q]
      by_cases hq : q ∈ S
      · simpa only [Set.indicator_of_mem hq, elementaryClass] using he
      · simp only [Set.indicator_of_notMem hq]
    rw [heq, map_zero]
    exact Submodule.zero_mem _

/-- A supported integral admits an adapted version for the given filtration.
Only positive input times matter, and `t = 0` is included. The default chosen
representative need not itself be measurable for the uncompleted `F t`. -/
theorem walshT_adapted (hW : IsWhiteNoise P F W) (t : ℝ≥0)
    (G : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G)
    (hsupport : ∀ s y ω, 0 < s → (t : ℝ) < s → G s y ω = 0) :
    ∃ X : Ω → ℝ, StronglyMeasurable[F t] X ∧ walshT hW G =ᵐ[P] X := by
  obtain ⟨R, hR⟩ := exists_restrictPredL2 (F := F) (P := P) (t : ℝ)
  let J := (walshL2 hW).toContinuousLinearMap.comp R
  let M : Submodule ℝ (PredL2 F P) := (lpMeas ℝ ℝ (F t) 2 P).comap J.toLinearMap
  have hclosed : IsClosed (M : Set (PredL2 F P)) :=
    (isClosed_aestronglyMeasurable (F.le t)).preimage J.continuous
  have hspan : Submodule.span ℝ (Set.range (elementaryClass (F := F) P)) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact restricted_elementary_adapted hW t R hR e
  have hall (f : PredL2 F P) : f ∈ M :=
    (closure_minimal hspan hclosed) (dense_elementary f)
  have heq : R (toPredL2 G hG) = toPredL2 G hG := by
    apply Subtype.ext
    apply Lp.ext
    have hpos : ∀ᵐ q ∂spaceTimeSample P, 0 < q.1 := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_lt measurable_const measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact Filter.Eventually.of_forall fun _ => hs
    filter_upwards [hR (toPredL2 G hG), toPredL2_ae G hG, hpos] with q hr hg hq
    rw [hr]
    by_cases ht : q.1 ≤ t
    · exact Set.indicator_of_mem
        (show q ∈ {q : ℝ × ℝ × Ω | q.1 ∈ Set.Ioc 0 (t : ℝ)} from ⟨hq, ht⟩) _
    · rw [Set.indicator_of_notMem (by simpa only [Set.mem_ofPred_eq, Set.mem_Ioc,
        not_and] using fun _ => ht), hg]
      exact (hsupport _ _ _ hq (lt_of_not_ge ht)).symm
  have hm : AEStronglyMeasurable[F t] (fun ω => walshL2 hW (toPredL2 G hG) ω) P := by
    have h := hall (toPredL2 G hG)
    change AEStronglyMeasurable[F t] (fun ω => walshL2 hW (R (toPredL2 G hG)) ω) P at h
    rwa [heq] at h
  obtain ⟨X, hXm, hXa⟩ := hm
  exact ⟨X, hXm, (walshT_ae_eq hW G hG).trans hXa⟩

private theorem walshT_sub_eLpNorm (hW : IsWhiteNoise P F W)
    (G G' : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) (hG' : InDomain F P G') :
    eLpNorm (fun ω => walshT hW G ω - walshT hW G' ω) 2 P =
      eLpNorm (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2 - G' q.1 q.2.1 q.2.2)
        2 (spaceTimeSample P) := by
  exact WalshIntegral.IntegralIncrements.walshT_sub_eLpNorm hW G G' hG hG'

set_option linter.unusedSectionVars false in
private theorem field_sq_lintegral (G : ℝ → ℝ → Ω → ℝ)
    (hm : Measurable (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)) :
    eLpNorm (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) 2 (spaceTimeSample P) ^ 2 =
      ∫⁻ q : ℝ × ℝ × Ω, ENNReal.ofReal (G q.1 q.2.1 q.2.2 ^ 2) ∂spaceTimeSample P := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    using eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      hm.aestronglyMeasurable

private theorem bounded_kernel_sq_le (a : ℝ → ℝ → ℝ)
    (ha : Measurable (fun z : ℝ × ℝ => a z.1 z.2)) (n : ℕ)
    (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    eLpNorm (fun q : ℝ × ℝ × Ω => a q.1 q.2.1 * clipField n Φ q.1 q.2.1 q.2.2)
        2 (spaceTimeSample P) ^ 2 ≤
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (a z.1 z.2 ^ 2) ∂timeSpaceVolume) *
        ENNReal.ofReal (n : ℝ) ^ 2 := by
  have hm : Measurable (fun q : ℝ × ℝ × Ω =>
      a q.1 q.2.1 * clipField n Φ q.1 q.2.1 q.2.2) :=
    ((ha.comp (measurable_coord F)).mul (clipField_measurable n Φ hΦ)).mono
      (predictableSigma_le F) le_rfl
  rw [field_sq_lintegral (fun s y ω => a s y * clipField n Φ s y ω) hm, spaceTimeSample_eq_map,
    lintegral_map (hm.pow_const 2).ennreal_ofReal MeasurableEquiv.prodAssoc.measurable]
  have hm' : Measurable (fun q : (ℝ × ℝ) × Ω =>
      a q.1.1 q.1.2 * clipField n Φ q.1.1 q.1.2 q.2) :=
    hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  change (∫⁻ q : (ℝ × ℝ) × Ω,
    ENNReal.ofReal ((a q.1.1 q.1.2 * clipField n Φ q.1.1 q.1.2 q.2) ^ 2)
      ∂timeSpaceVolume.prod P) ≤ _
  rw [lintegral_prod _ (hm'.pow_const 2).ennreal_ofReal.aemeasurable,
    ← lintegral_mul_const _ (ha.pow_const 2).ennreal_ofReal]
  apply lintegral_mono
  intro z
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (a z.1 z.2 ^ 2) *
        ENNReal.ofReal (n : ℝ) ^ 2 ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_pow (Nat.cast_nonneg n)]
      apply mul_le_mul le_rfl _ bot_le bot_le
      apply ENNReal.ofReal_le_ofReal
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg n)).mpr (clipField_abs_le n Φ z.1 z.2 ω)
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]

/-- Joint L² continuity of the bounded stochastic convolution on all of `ℝ × ℝ`.
The preceding domain statement makes this norm convergence continuity of the
genuine L² classes, including at and below time zero. -/
theorem walshT_clipField_l2Continuous (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (n : ℕ) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) (z : ℝ × ℝ) :
    Tendsto (fun z' : ℝ × ℝ => eLpNorm (fun ω =>
      walshT hW (kernelField K z'.1 z'.2 (clipField n Φ)) ω -
        walshT hW (kernelField K z.1 z.2 (clipField n Φ)) ω) 2 P)
      (𝓝 z) (𝓝 0) := by
  let D (z' : ℝ × ℝ) := eLpNorm (fun ω =>
    walshT hW (kernelField K z'.1 z'.2 (clipField n Φ)) ω -
      walshT hW (kernelField K z.1 z.2 (clipField n Φ)) ω) 2 P
  have hb (z' : ℝ × ℝ) : D z' ^ 2 ≤
      (∫⁻ w : ℝ × ℝ, ENNReal.ofReal
        ((K.K z'.1 z'.2 w.1 w.2 - K.K z.1 z.2 w.1 w.2) ^ 2) ∂timeSpaceVolume) *
          ENNReal.ofReal (n : ℝ) ^ 2 := by
    dsimp only [D]
    rw [walshT_sub_eLpNorm hW _ _ (kernelField_clipField_inDomain K n Φ hΦ _ _)
      (kernelField_clipField_inDomain K n Φ hΦ _ _)]
    simp only [kernelField, ← sub_mul]
    exact bounded_kernel_sq_le (fun s y => K.K z'.1 z'.2 s y - K.K z.1 z.2 s y)
      ((K.measurable.comp ((measurable_const (a := z')).prodMk measurable_id)).sub
        (K.measurable.comp ((measurable_const (a := z)).prodMk measurable_id))) n Φ hΦ
  have hupper := ENNReal.Tendsto.mul_const (K.tendsto_sq z)
    (Or.inr (ne_of_lt (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) :
      (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal (n : ℝ) ^ 2 ≠ ⊤)
  simp only [zero_mul] at hupper
  have hsq : Tendsto (fun z' => D z' ^ 2) (𝓝 z) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => bot_le) hb
  simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one,
    ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)] using
    hsq.ennrpow_const ((2 : ℝ)⁻¹)

/-- Squared L² error between the truncated and original stochastic convolutions. -/
def truncationError (hW : IsWhiteNoise P F W) (K : CausalKernel)
    (Φ : ℝ → ℝ → Ω → ℝ) (n : ℕ) (t x : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun ω => walshT hW (kernelField K t x (clipField n Φ)) ω -
    walshT hW (kernelField K t x Φ) ω) 2 P ^ 2

/-- The isometry expresses the stochastic error as a deterministic variance. -/
theorem truncationError_eq_kernelVariance (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (n : ℕ) (t x : ℝ) (hfin : kernelVariance P K Φ t x < ⊤) :
    truncationError hW K Φ n t x =
      kernelVariance P K (fun s y ω => clipField n Φ s y ω - Φ s y ω) t x := by
  have hclip := kernelField_clipField_inDomain (P := P) K n Φ hΦ t x
  have horig := (kernelField_inDomain_iff K t x Φ hΦ).mpr hfin
  have hres := (clipField_measurable n Φ hΦ).sub hΦ
  rw [truncationError, walshT_sub_eLpNorm hW _ _ hclip horig,
    field_sq_lintegral (fun s y ω => kernelField K t x (clipField n Φ) s y ω -
      kernelField K t x Φ s y ω)
      ((hclip.1.sub horig.1).mono (predictableSigma_le F) le_rfl),
    kernelVariance_eq_lintegral K t x _ hres]
  simp only [kernelField, mul_sub]

/-- On the full the corresponding interface domain, each squared truncation error is Borel in the output. -/
theorem truncationError_measurable (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (hfin : ∀ t x, kernelVariance P K Φ t x < ⊤) (n : ℕ) :
    Measurable (fun z : ℝ × ℝ => truncationError hW K Φ n z.1 z.2) := by
  simp_rw [truncationError_eq_kernelVariance hW K Φ hΦ n _ _ (hfin _ _),
    kernelVariance_eq_lintegral K _ _
      (fun s y ω => clipField n Φ s y ω - Φ s y ω) ((clipField_measurable n Φ hΦ).sub hΦ)]
  have hm := ((clipField_measurable n Φ hΦ).sub hΦ).mono (predictableSigma_le F) le_rfl
  have hjoint : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ × Ω) =>
      ENNReal.ofReal ((K.K q.1.1 q.1.2 q.2.1 q.2.2.1 *
        (clipField n Φ q.2.1 q.2.2.1 q.2.2.2 - Φ q.2.1 q.2.2.1 q.2.2.2)) ^ 2)) :=
    (((K.measurable.comp (measurable_fst.prodMk
      (measurable_snd.fst.prodMk measurable_snd.snd.fst))).mul
        (hm.comp measurable_snd)).pow_const 2).ennreal_ofReal
  let : SFinite (spaceTimeSample P) := by unfold spaceTimeSample; infer_instance
  exact hjoint.lintegral_prod_right'

set_option linter.unusedSectionVars false in
private theorem clip_residual_abs (n : ℕ) (Φ : ℝ → ℝ → Ω → ℝ)
    (s y : ℝ) (ω : Ω) :
    |clipField n Φ s y ω - Φ s y ω| = max (|Φ s y ω| - (n : ℝ)) 0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [clipField, abs_eq_max_neg, max_def, min_def]
  split_ifs <;> linarith

set_option linter.unusedSectionVars false in
private theorem clip_eventually_eq (Φ : ℝ → ℝ → Ω → ℝ) (s y : ℝ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, clipField n Φ s y ω = Φ s y ω := by
  obtain ⟨N, hN⟩ := exists_nat_ge |Φ s y ω|
  apply eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  have hb : |Φ s y ω| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  rw [abs_le] at hb
  simp only [clipField, min_eq_right hb.2, max_eq_right hb.1]

/-- At each finite-variance point the squared errors decrease with the clipping level. -/
theorem truncationError_antitone (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (t x : ℝ) (hfin : kernelVariance P K Φ t x < ⊤) :
    Antitone (fun n => truncationError hW K Φ n t x) := by
  intro n m hnm
  dsimp only
  rw [truncationError_eq_kernelVariance hW K Φ hΦ m t x hfin,
    truncationError_eq_kernelVariance hW K Φ hΦ n t x hfin,
    kernelVariance_eq_lintegral K t x _ ((clipField_measurable m Φ hΦ).sub hΦ),
    kernelVariance_eq_lintegral K t x _ ((clipField_measurable n Φ hΦ).sub hΦ)]
  apply lintegral_mono
  intro q
  apply ENNReal.ofReal_le_ofReal
  simp only [kernelField, mul_pow]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hres : |clipField m Φ q.1 q.2.1 q.2.2 - Φ q.1 q.2.1 q.2.2| ≤
      |clipField n Φ q.1 q.2.1 q.2.2 - Φ q.1 q.2.1 q.2.2| := by
    rw [clip_residual_abs, clip_residual_abs]
    exact max_le_max (sub_le_sub_left (Nat.cast_le.mpr hnm) _) le_rfl
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hres

/-- Dominated convergence gives vanishing error at every finite-variance point. -/
theorem truncationError_tendsto_zero (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (t x : ℝ) (hfin : kernelVariance P K Φ t x < ⊤) :
    Tendsto (fun n => truncationError hW K Φ n t x) atTop (𝓝 0) := by
  have hres (n : ℕ) := kernelField_measurable K t x
    (fun s y ω => clipField n Φ s y ω - Φ s y ω) ((clipField_measurable n Φ hΦ).sub hΦ)
  have hbound (n : ℕ) (q : ℝ × ℝ × Ω) :
      ENNReal.ofReal (kernelField K t x
        (fun s y ω => clipField n Φ s y ω - Φ s y ω) q.1 q.2.1 q.2.2 ^ 2) ≤
      ENNReal.ofReal (kernelField K t x Φ q.1 q.2.1 q.2.2 ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    simp only [kernelField, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hr : |clipField n Φ q.1 q.2.1 q.2.2 - Φ q.1 q.2.1 q.2.2| ≤
        |Φ q.1 q.2.1 q.2.2| := by
      rw [clip_residual_abs]
      exact max_le (sub_le_self _ (Nat.cast_nonneg n)) (abs_nonneg _)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hr
  have hl := tendsto_lintegral_of_dominated_convergence
    (μ := spaceTimeSample P)
    (F := fun n (q : ℝ × ℝ × Ω) => ENNReal.ofReal (kernelField K t x
      (fun s y ω => clipField n Φ s y ω - Φ s y ω) q.1 q.2.1 q.2.2 ^ 2))
    (f := fun _ => 0)
    (fun q : ℝ × ℝ × Ω => ENNReal.ofReal (kernelField K t x Φ q.1 q.2.1 q.2.2 ^ 2))
    (fun n => (((hres n).mono (predictableSigma_le F) le_rfl).pow_const 2).ennreal_ofReal)
    (fun n => Filter.Eventually.of_forall (hbound n))
    (by rw [← kernelVariance_eq_lintegral K t x Φ hΦ]; exact hfin.ne)
    (Filter.Eventually.of_forall fun q => by
      apply tendsto_const_nhds.congr'
      filter_upwards [clip_eventually_eq Φ q.1 q.2.1 q.2.2] with n hn
      simp only [kernelField, hn, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0),
        ENNReal.ofReal_zero])
  simpa only [truncationError_eq_kernelVariance hW K Φ hΦ _ t x hfin,
    kernelVariance_eq_lintegral K t x
      (fun s y ω => clipField _ Φ s y ω - Φ s y ω) ((clipField_measurable _ Φ hΦ).sub hΦ),
    lintegral_zero] using hl

/-- Countable Borel selection at the summable squared-error thresholds `2^(-4j)`.
Apply with `r n z = truncationError hW K Φ n z.1 z.2`; no uniform convergence
or local boundedness of the original convolution is required. -/
theorem exists_borel_error_indices (r : ℕ → (ℝ × ℝ) → ℝ≥0∞)
    (hmeas : ∀ n, Measurable (r n))
    (hlim : ∀ z, Tendsto (fun n => r n z) atTop (𝓝 0)) :
    ∃ N : ℕ → (ℝ × ℝ) → ℕ,
      (∀ j, Measurable (N j)) ∧
      ∀ j z, r (N j z) z ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j) := by
  classical
  have hex (j : ℕ) (z : ℝ × ℝ) : ∃ n, r n z ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j) := by
    have hp : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ (4 * j) :=
      ENNReal.pow_pos (by norm_num) _
    obtain ⟨n, hn⟩ := ((hlim z).eventually (gt_mem_nhds hp)).exists
    exact ⟨n, hn.le⟩
  refine ⟨fun j z => Nat.find (hex j z), ?_, ?_⟩
  · intro j
    exact measurable_find (hex j) (fun n => measurableSet_le (hmeas n) measurable_const)
  · intro j z
    exact Nat.find_spec (hex j z)

/-- Select from a countable family using a deterministic time-space index. -/
def borelSelectField (U : ℕ → ℝ → ℝ → Ω → ℝ) (N : (ℝ × ℝ) → ℕ) :
    ℝ → ℝ → Ω → ℝ :=
  fun t x ω => U (N (t, x)) t x ω

/-- Countable gluing is predictable because Borel output coordinates are predictable. -/
theorem borelSelectField_measurable (U : ℕ → ℝ → ℝ → Ω → ℝ)
    (hU : ∀ n, Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => U n q.1 q.2.1 q.2.2))
    (N : (ℝ × ℝ) → ℕ) (hN : Measurable N) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => borelSelectField U N q.1 q.2.1 q.2.2) := by
  let : MeasurableSpace (ℝ × ℝ × Ω) := predictableSigma F
  have hm : Measurable (fun p : ℕ × (ℝ × ℝ × Ω) => U p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    measurable_from_prod_countable_right hU
  exact hm.comp ((hN.comp (measurable_coord F)).prodMk measurable_id)

/-- Pointwise limit, defined to be zero exactly where no finite real limit exists. -/
def limitField (V : ℕ → ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ := by
  classical
  exact fun t x ω => if h : ∃ a : ℝ, Tendsto (fun j => V j t x ω) atTop (𝓝 a)
    then Classical.choose h else 0

/-- The convergence set and the zero-totalized limit are predictable. -/
theorem limitField_measurable (V : ℕ → ℝ → ℝ → Ω → ℝ)
    (hV : ∀ j, Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => V j q.1 q.2.1 q.2.2)) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => limitField V q.1 q.2.1 q.2.2) := by
  classical
  let : MeasurableSpace (ℝ × ℝ × Ω) := predictableSigma F
  let S : Set (ℝ × ℝ × Ω) := {q | ∃ a : ℝ,
    Tendsto (fun j => V j q.1 q.2.1 q.2.2) atTop (𝓝 a)}
  have hS : MeasurableSet S := measurableSet_exists_tendsto hV
  have hm : Measurable (fun q : ℝ × ℝ × Ω =>
      limUnder atTop (fun j => V j q.1 q.2.1 q.2.2)) :=
    (StronglyMeasurable.limUnder (fun j => (hV j).stronglyMeasurable)).measurable
  convert hm.indicator hS using 1
  funext q
  by_cases hc : ∃ a : ℝ, Tendsto (fun j => V j q.1 q.2.1 q.2.2) atTop (𝓝 a)
  · have hq : q ∈ S := hc
    simp only [limitField, dite_eq_left hc, Set.indicator_of_mem hq]
    exact (Classical.choose_spec hc).limUnder_eq.symm
  · have hq : q ∉ S := hc
    simp only [limitField, dite_eq_right hc, Set.indicator_of_notMem hq]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Summable L² errors identify the limit at each output point.
The order of quantifiers deliberately does not assert indistinguishability. -/
theorem ae_eq_limitField_of_error_le (X : ℝ → ℝ → Ω → ℝ)
    (V : ℕ → ℝ → ℝ → Ω → ℝ)
    (hX : ∀ t x, AEStronglyMeasurable (X t x) P)
    (hV : ∀ j t x, AEStronglyMeasurable (V j t x) P)
    (herr : ∀ j t x, eLpNorm (fun ω => V j t x ω - X t x ω) 2 P ^ 2 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ (4 * j)) :
    ∀ t x, X t x =ᵐ[P] limitField V t x := by
  classical
  intro t x
  have hb (j : ℕ) : eLpNorm (fun ω => V j t x ω - X t x ω) 2 P ≤
      ((2 : ℝ≥0∞)⁻¹) ^ j := by
    have hs : eLpNorm (fun ω => V j t x ω - X t x ω) 2 P ^ 2 ≤
        (((2 : ℝ≥0∞)⁻¹) ^ j) ^ 2 := by
      apply (herr j t x).trans
      rw [← pow_mul]
      exact pow_le_pow_of_le_one bot_le (by norm_num) (by omega)
    have hr := ENNReal.rpow_le_rpow hs (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] using hr
  have hsum : (∑' j, eLpNorm (fun ω => V j t x ω - X t x ω) 2 P) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' j, ((2 : ℝ≥0∞)⁻¹) ^ j := ENNReal.tsum_le_tsum hb
      _ = 2 := ENNReal.tsum_geometric_two
      _ < ⊤ := by norm_num
  have hae := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hsum
  filter_upwards [hae] with ω hω
  have hl : Tendsto (fun j => V j t x ω) atTop (𝓝 (X t x ω)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hω.tendsto_atTop_zero
  have hc : ∃ a : ℝ, Tendsto (fun j => V j t x ω) atTop (𝓝 a) := ⟨_, hl⟩
  simp only [limitField, dite_eq_left hc]
  exact tendsto_nhds_unique hl (Classical.choose_spec hc)

private theorem predictable_tail (a : ℝ≥0) {B : Set Ω} (hB : MeasurableSet[F a] B) :
    MeasurableSet[predictableSigma F]
      (Set.Ioi (a : ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ B)) := by
  have heq : Set.Ioi (a : ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ B) =
      ⋃ n : ℕ, Set.Ioc (a : ℝ) ((a + (n + 1) : ℝ≥0) : ℝ) ×ˢ (Set.univ ×ˢ B) := by
    ext q
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioc, Set.mem_iUnion,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    constructor
    · rintro ⟨ha, hAB⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (q.1 - a)
      exact ⟨n, ⟨ha, by linarith⟩, hAB⟩
    · rintro ⟨n, ⟨ha, _⟩, hAB⟩
      exact ⟨ha, hAB⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact MeasurableSpace.measurableSet_generateFrom
    (Or.inl ⟨a, a + (n + 1), Set.univ, B, by simp, MeasurableSet.univ, hB, rfl⟩)

private theorem predictable_after (a : ℝ≥0) (Y : Ω → ℝ)
    (hY : StronglyMeasurable[F a] Y) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => if (a : ℝ) < q.1 then Y q.2.2 else 0) := by
  classical
  have hD : MeasurableSet[predictableSigma F] {q : ℝ × ℝ × Ω | (a : ℝ) < q.1} :=
    measurableSet_lt measurable_const (measurable_coord F).fst
  intro B hB
  have hpre := predictable_tail a (hY.measurable hB)
  by_cases hzero : (0 : ℝ) ∈ B
  · convert hpre.union hD.compl using 1
    ext q
    by_cases hq : (a : ℝ) < q.1 <;> simp [hq, hzero]
  · convert hpre using 1
    ext q
    by_cases hq : (a : ℝ) < q.1 <;> simp [hq, hzero]

private theorem exists_left_rational_approx {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ × ℝ → E) (hf : Continuous f) (z : ℝ × ℝ) (ht : 0 < z.1)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ r s : ℚ, 0 ≤ (r : ℝ) ∧ (r : ℝ) < z.1 ∧
      edist (f ((r : ℝ), (s : ℝ))) (f z) ^ 2 ≤ ε := by
  have hlim : Tendsto (fun z' => edist (f z') (f z) ^ 2) (𝓝 z) (𝓝 0) := by
    simpa only [Function.comp_def, edist_self, zero_pow (by decide : 2 ≠ 0)] using ((ENNReal.continuous_pow 2).comp (hf.edist (continuous_const (y := f z)))).tendsto z
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hlim.eventually (gt_mem_nhds hε))
  obtain ⟨r, hr, hrt⟩ := exists_rat_btwn
    (show max (0 : ℝ) (z.1 - δ / 2) < z.1 from max_lt ht (by linarith))
  obtain ⟨s, hs₁, hs₂⟩ := exists_rat_btwn (show z.2 - δ / 2 < z.2 + δ / 2 by linarith)
  refine ⟨r, s, (le_max_left _ _).trans hr.le, hrt, ?_⟩
  refine (hball ?_).le
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
  have hr' := (le_max_right _ _).trans_lt hr
  constructor <;> constructor <;> linarith

/-- The left-grid construction for an adapted, jointly L²-continuous field.
Choose adapted versions on a countable rational grid and Borel-select points
strictly to the left that meet summable squared-error bounds. Predictable
countable gluing suffices without a left-continuous filtration. -/
theorem exists_predictable_modification_of_l2Continuous
    (X : ℝ → ℝ → Ω → ℝ)
    (hmem : ∀ t x, MemLp (X t x) 2 P)
    (hadapted : ∀ (t : ℝ≥0) (x : ℝ), ∃ Y : Ω → ℝ,
      StronglyMeasurable[F t] Y ∧ X t x =ᵐ[P] Y)
    (hzero : ∀ t x, t ≤ 0 → X t x =ᵐ[P] (fun _ => 0))
    (hcont : ∀ z : ℝ × ℝ,
      Tendsto (fun z' : ℝ × ℝ => eLpNorm
        (fun ω => X z'.1 z'.2 ω - X z.1 z.2 ω) 2 P) (𝓝 z) (𝓝 0)) :
    ∃ U : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => U q.1 q.2.1 q.2.2) ∧
        ∀ t x, X t x =ᵐ[P] U t x := by
  classical
  let f (z : ℝ × ℝ) : Lp ℝ 2 P := (hmem z.1 z.2).toLp (X z.1 z.2)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun z' : ℝ × ℝ => X z'.1 z'.2)
      (fun z' => hmem z'.1 z'.2) (X z.1 z.2) (hmem z.1 z.2)).mpr (hcont z)
  obtain ⟨c, hc⟩ := exists_surjective_nat (ℚ × ℚ)
  let a (n : ℕ) : ℝ≥0 := Real.toNNReal ((c n).1 : ℝ)
  let b (n : ℕ) : ℝ := ((c n).2 : ℝ)
  choose Y hY hXY using (fun n => hadapted (a n) (b n))
  let U (n : ℕ) (t x : ℝ) (ω : Ω) : ℝ := if (a n : ℝ) < t then Y n ω else 0
  have hU (n : ℕ) : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => U n q.1 q.2.1 q.2.2) := predictable_after (a n) (Y n) (hY n)
  let pred (j : ℕ) (z : ℝ × ℝ) (n : ℕ) : Prop := z.1 ≤ 0 ∨
    (a n : ℝ) < z.1 ∧ edist (f ((a n : ℝ), b n)) (f z) ^ 2 ≤ (2⁻¹ : ℝ≥0∞) ^ (4 * j)
  have hex (j : ℕ) (z : ℝ × ℝ) : ∃ n, pred j z n := by
    by_cases ht : z.1 ≤ 0
    · exact ⟨0, Or.inl ht⟩
    · obtain ⟨r, s, hr0, hrt, herr⟩ := exists_left_rational_approx f hf z (lt_of_not_ge ht)
        ((2⁻¹ : ℝ≥0∞) ^ (4 * j)) (ENNReal.pow_pos (by norm_num) _)
      obtain ⟨n, hn⟩ := hc (r, s)
      refine ⟨n, Or.inr ?_⟩
      simpa only [a, b, hn, Real.coe_toNNReal _ hr0] using And.intro hrt herr
  have hpred (j n : ℕ) : MeasurableSet {z : ℝ × ℝ | pred j z n} := by
    exact (measurableSet_le measurable_fst measurable_const).union
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le (((ENNReal.continuous_pow 2).comp
          (continuous_const.edist hf)).measurable) measurable_const))
  let N (j : ℕ) (z : ℝ × ℝ) : ℕ := Nat.find (hex j z)
  have hN (j : ℕ) : Measurable (N j) := measurable_find (hex j) (hpred j)
  let V (j : ℕ) := borelSelectField U (N j)
  have hV (j : ℕ) : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => V j q.1 q.2.1 q.2.2) :=
    borelSelectField_measurable U hU (N j) (hN j)
  have herr (j : ℕ) (t x : ℝ) :
      eLpNorm (fun ω => V j t x ω - X t x ω) 2 P ^ 2 ≤ (2⁻¹ : ℝ≥0∞) ^ (4 * j) := by
    have hn := Nat.find_spec (hex j (t, x))
    by_cases ht : t ≤ 0
    · have hVzero : V j t x = fun _ => 0 := by
        funext ω
        have hnt : ¬(a (N j (t, x)) : ℝ) < t := not_lt.mpr ((a _).coe_nonneg.trans' ht)
        simp only [V, borelSelectField, U, ite_eq_right hnt]
      have he : (fun ω => V j t x ω - X t x ω) =ᵐ[P] (fun _ => (0 : ℝ)) := by
        filter_upwards [hzero t x ht] with ω hω
        simp only [hVzero, hω, sub_self]
      rw [eLpNorm_congr_ae he]
      change eLpNorm (0 : Ω → ℝ) 2 P ^ 2 ≤ _
      simp
    · obtain ⟨ha, he⟩ := hn.resolve_left ht
      change (a (N j (t, x)) : ℝ) < t at ha
      have hnorm : eLpNorm (fun ω => V j t x ω - X t x ω) 2 P =
          edist (f ((a (N j (t, x)) : ℝ), b (N j (t, x)))) (f (t, x)) := by
        rw [Lp.edist_toLp_toLp]
        apply eLpNorm_congr_ae
        filter_upwards [hXY (N j (t, x))] with ω hω
        simp only [V, borelSelectField, U, ite_eq_left ha, Pi.sub_apply, hω]
      rwa [hnorm]
  refine ⟨limitField V, limitField_measurable V hV, ?_⟩
  apply ae_eq_limitField_of_error_le X V (fun t x => (hmem t x).aestronglyMeasurable)
    _ herr
  intro j t x
  exact (((hV j).mono (predictableSigma_le F) le_rfl).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable

/-- Predictable versions of all bounded truncations, supplied by left grids.
There is no finite-variance assumption on the original, unclipped field here. -/
theorem exists_predictable_clipField_modifications (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2)) :
    ∃ U : ℕ → ℝ → ℝ → Ω → ℝ,
      (∀ n, Measurable[predictableSigma F]
        (fun q : ℝ × ℝ × Ω => U n q.1 q.2.1 q.2.2)) ∧
      ∀ n t x, walshT hW (kernelField K t x (clipField n Φ)) =ᵐ[P] U n t x := by
  have hd (n : ℕ) (t x : ℝ) := kernelField_clipField_inDomain (P := P) K n Φ hΦ t x
  have hmods (n : ℕ) : ∃ U : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => U q.1 q.2.1 q.2.2) ∧
      ∀ t x, walshT hW (kernelField K t x (clipField n Φ)) =ᵐ[P] U t x := by
    apply exists_predictable_modification_of_l2Continuous
      (fun t x => walshT hW (kernelField K t x (clipField n Φ)))
    · intro t x
      exact (memLp_congr_ae (walshT_ae_eq hW _ (hd n t x))).mpr (Lp.memLp _)
    · intro t x
      apply walshT_adapted hW t _ (hd n t x)
      intro s y ω _ hts
      simp only [kernelField, K.causal t x s y (Or.inr hts.le), zero_mul]
    · intro t x ht
      have hfield : kernelField K t x (clipField n Φ) = fun _ _ _ => 0 := by
        funext s y ω
        have hcausal : s ≤ 0 ∨ t ≤ s := by
          by_cases hs : s ≤ 0
          · exact Or.inl hs
          · exact Or.inr (ht.trans (le_of_not_ge hs))
        simp only [kernelField, K.causal t x s y hcausal, zero_mul]
      have h0 : walshT hW (fun _ _ _ => 0) =ᵐ[P] (fun _ => 0) := by
        simpa only [zero_mul] using walshT_smul hW 0 _ (hd n t x)
      rwa [hfield]
    · exact walshT_clipField_l2Continuous hW K n Φ hΦ
  choose U hUm hUeq using hmods
  exact ⟨U, hUm, hUeq⟩

/-- the corresponding interface in the exact full-domain form consumed by a predictable convolution interface.
Instantiate the kernel with the cut-off heat kernel and identify `kernelVariance`
with the corresponding variance integral; there is no continuity hypothesis on the original input
or its stochastic convolution, and no additional integrability hypothesis. -/
theorem exists_predictable_modification (hW : IsWhiteNoise P F W)
    (K : CausalKernel) (Φ : ℝ → ℝ → Ω → ℝ)
    (hΦ : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Φ q.1 q.2.1 q.2.2))
    (hfin : ∀ t x, kernelVariance P K Φ t x < ⊤) :
    ∃ Ψ : ℝ → ℝ → Ω → ℝ,
      Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => Ψ q.1 q.2.1 q.2.2) ∧
        ∀ t x, walshT hW (kernelField K t x Φ) =ᵐ[P] Ψ t x := by
  obtain ⟨U, hUm, hUeq⟩ := exists_predictable_clipField_modifications hW K Φ hΦ
  obtain ⟨N, hNm, hNerr⟩ := exists_borel_error_indices
    (fun n z => truncationError hW K Φ n z.1 z.2)
    (fun n => truncationError_measurable hW K Φ hΦ hfin n)
    (fun z => truncationError_tendsto_zero hW K Φ hΦ z.1 z.2 (hfin z.1 z.2))
  let V (j : ℕ) := borelSelectField U (N j)
  have hVm (j : ℕ) : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => V j q.1 q.2.1 q.2.2) :=
    borelSelectField_measurable U hUm (N j) (hNm j)
  refine ⟨limitField V, limitField_measurable V hVm, ?_⟩
  apply ae_eq_limitField_of_error_le (fun t x => walshT hW (kernelField K t x Φ)) V
  · intro t x
    have hd := (kernelField_inDomain_iff K t x Φ hΦ).mpr (hfin t x)
    exact (Lp.aestronglyMeasurable _).congr (walshT_ae_eq hW _ hd).symm
  · intro j t x
    exact (((hVm j).mono (predictableSigma_le F) le_rfl).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · intro j t x
    have heq : (fun ω => V j t x ω - walshT hW (kernelField K t x Φ) ω) =ᵐ[P]
        (fun ω => walshT hW (kernelField K t x (clipField (N j (t, x)) Φ)) ω -
          walshT hW (kernelField K t x Φ) ω) :=
      (hUeq (N j (t, x)) t x).symm.sub Filter.EventuallyEq.rfl
    rw [eLpNorm_congr_ae heq]
    exact hNerr j (t, x)

end WalshIntegral.Modification
