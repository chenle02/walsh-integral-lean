module

public import WalshIntegralChallenge.Reference.WalshIntegral.Rio
public import WalshIntegralChallenge.Reference.WalshIntegral.Integral
public import Mathlib.Order.Interval.Set.Union

@[expose] public section

/-!
# Mixed-norm moment estimates for every real p ≥ 2. The explicit squared-norm constant is `(p - 1) * gaussianMoment p ^ 2` and grows quadratically in p. No sharp linear-in-p bound is claimed.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace WalshIntegral.MomentBound

open WalshIntegral.WhiteNoise WalshIntegral.Predictable WalshIntegral.Integral

/-- The standard Gaussian L^p norm, expressed using the real moment integral.
Only positive p is used as a norm; outside that range this is a total formula. -/
def gaussianMoment (p : ℝ) : ℝ :=
  (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)

/-- The finite real constant supplied by the Rio and Gaussian slab argument. -/
def bdgConst (p : ℝ) : ℝ :=
  (p - 1) * gaussianMoment p ^ 2

/-- Gaussian absolute moments are integrable for every nonnegative real power. -/
theorem integrable_gaussianMoment_integrand {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs, id_def, ENNReal.toReal_ofReal hp] using
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal p)
      ENNReal.ofReal_ne_top).integrable_norm_rpow'

/-- The real moment definition agrees with the ENNReal norm used in the bounds. -/
theorem ofReal_gaussianMoment_eq_eLpNorm {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (gaussianMoment p) =
      eLpNorm (fun x : ℝ => x) (ENNReal.ofReal p) (gaussianReal 0 1) := by
  symm
  convert! (memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal p)
    ENNReal.ofReal_ne_top).eLpNorm_eq_integral_rpow_norm
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top using 1
  simp [gaussianMoment, Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le, one_div]

/-- A standard Gaussian has strictly positive L^p norm for positive real p. -/
theorem gaussianMoment_pos {p : ℝ} (hp : 0 < p) : 0 < gaussianMoment p := by
  have : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  apply ENNReal.ofReal_pos.mp
  rw [ofReal_gaussianMoment_eq_eLpNorm hp]
  apply pos_iff_ne_zero.mpr
  intro hz
  have hae := (eLpNorm_eq_zero_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hp))).mp hz
  have hne : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
    simp only [ae_iff, not_not, measure_singleton, Set.ofPred_eq_eq_singleton]
  obtain ⟨x, hx, hnx⟩ := (hae.and hne).exists
  exact hnx hx

/-- Nonnegativity on the whole exponent range required by the corresponding interface. -/
theorem bdgConst_nonneg {p : ℝ} (hp : 2 ≤ p) : 0 ≤ bdgConst p := by
  exact mul_nonneg (by linarith) (sq_nonneg _)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Squared L² in positive time-space of the samplewise L^p norm. -/
def mixedNormSq (P : Measure Ω) (p : ℝ) (G : ℝ → ℝ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P ^ 2 ∂timeSpaceVolume

/-- A finite sum of bounded predictable elementary fields. -/
def elementarySum {F : Filtration ℝ≥0 mΩ} {n : ℕ}
    (e : Fin n → Elementary F) : ℝ → ℝ → Ω → ℝ :=
  fun s y ω => ∑ j, (e j).field s y ω

/-- The sum of chosen representatives of the corresponding elementary integrals.
All moment assertions are insensitive to these representative choices. -/
def elementarySumIntegral {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (W : H →L[ℝ] Lp ℝ 2 P) {n : ℕ}
    (e : Fin n → Elementary F) : Ω → ℝ :=
  fun ω => ∑ j, elementaryIntegral W (e j) ω

/-- Conditional variance for disjoint spatial cells on the common slab `(s,t]`.
Each cell has finite measure, so `toReal` here loses no infinite mass. -/
def slabVariance {F : Filtration ℝ≥0 mΩ} {n : ℕ}
    (s t : ℝ≥0) (e : Fin n → Elementary F) : Ω → ℝ :=
  fun ω => ((t : ℝ) - (s : ℝ)) *
    ∑ j, (volume (e j).A).toReal * (e j).coeff ω ^ 2

/-- Clip amplitude at n and restrict to the increasing box `(0,n] × [-n,n]`.
The zero truncation is the zero field, including at nonpositive times. -/
def truncateField (n : ℕ) (G : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ :=
  fun s y ω => if 0 < s ∧ s ≤ (n : ℝ) ∧ -(n : ℝ) ≤ y ∧ y ≤ (n : ℝ)
    then max (-(n : ℝ)) (min (n : ℝ) (G s y ω)) else 0

variable {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {W : H →L[ℝ] Lp ℝ 2 P}

private theorem measurable_sample_eLpNorm {p : ℝ} (hp : 0 < p)
    {G : ℝ → ℝ → Ω → ℝ}
    (hG : Measurable (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)) :
    Measurable (fun z : ℝ × ℝ => eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × Ω => G q.1.1 q.1.2 q.2) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have heq : (fun z : ℝ × ℝ => eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P) =
      (fun z => (∫⁻ ω, ‖G z.1 z.2 ω‖ₑ ^ (ENNReal.ofReal p).toReal ∂P) ^
        (1 / (ENNReal.ofReal p).toReal)) := by
    funext z
    exact eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [heq]
  exact (hm.enorm.pow_const _).lintegral_prod_right.pow_const _

private theorem truncateField_measurable (n : ℕ) {G : ℝ → ℝ → Ω → ℝ}
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)) :
    Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => truncateField n G q.1 q.2.1 q.2.2) := by
  have hc := measurable_coord F
  have hs : MeasurableSet[predictableSigma F]
      {q : ℝ × ℝ × Ω | 0 < q.1 ∧ q.1 ≤ (n : ℝ) ∧ -(n : ℝ) ≤ q.2.1 ∧ q.2.1 ≤ (n : ℝ)} :=
    (measurableSet_lt measurable_const hc.fst).inter
      ((measurableSet_le hc.fst measurable_const).inter
        ((measurableSet_le measurable_const hc.snd).inter
          (measurableSet_le hc.snd measurable_const)))
  exact Measurable.ite hs (measurable_const.max (measurable_const.min hG)) measurable_const

set_option linter.unusedSectionVars false in
private theorem truncateField_abs_le (n : ℕ) (G : ℝ → ℝ → Ω → ℝ) (s y : ℝ) (ω : Ω) :
    |truncateField n G s y ω| ≤ |G s y ω| ∧
      |truncateField n G s y ω - G s y ω| ≤ |G s y ω| := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg := le_abs_self (G s y ω)
  have hg' := neg_abs_le (G s y ω)
  unfold truncateField
  split_ifs
  · simp only [max_def, min_def]
    split_ifs <;> constructor <;> rw [abs_le] <;> constructor <;> linarith
  · simp

set_option linter.unusedSectionVars false in
private theorem truncateField_eventually_eq (G : ℝ → ℝ → Ω → ℝ) {s : ℝ}
    (hs : 0 < s) (y : ℝ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, truncateField n G s y ω = G s y ω := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max s (max |y| |G s y ω|))
  apply eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : s ≤ n := (le_max_left _ _).trans (hN.trans hNn)
  have hyn : |y| ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans (hN.trans hNn)
  have hgn : |G s y ω| ≤ n :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans (hN.trans hNn)
  simp only [abs_le] at hyn hgn
  simp [truncateField, hs, hsn, hyn.1, hyn.2, min_eq_right hgn.2, max_eq_right hgn.1]

/-- Sample L^p dominates sample L² on a probability space. Tonelli therefore
turns finite mixed norm and predictability into the exact domain of `walshT`. -/
theorem inDomain_of_mixedNormSq_lt_top {p : ℝ} (hp : 2 ≤ p)
    {G : ℝ → ℝ → Ω → ℝ}
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (hfin : mixedNormSq P p G < ⊤) : InDomain F P G := by
  refine ⟨hG, ?_⟩
  have hm := hG.mono (predictableSigma_le F) le_rfl
  have hm' : Measurable (fun q : (ℝ × ℝ) × Ω => G q.1.1 q.1.2 q.2) :=
    hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hsection (z : ℝ × ℝ) : Measurable (G z.1 z.2) :=
    hm'.comp (measurable_const.prodMk measurable_id)
  have hnorm (z : ℝ × ℝ) :
      (∫⁻ ω, ENNReal.ofReal (G z.1 z.2 ω ^ 2) ∂P) =
        eLpNorm (G z.1 z.2) 2 P ^ 2 := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) (hsection z).aestronglyMeasurable (μ := P)
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
      ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs] using h.symm
  rw [spaceTimeSample_eq_map, lintegral_map (hm.pow_const 2).ennreal_ofReal
    MeasurableEquiv.prodAssoc.measurable]
  change (∫⁻ q : (ℝ × ℝ) × Ω, ENNReal.ofReal (G q.1.1 q.1.2 q.2 ^ 2)
    ∂timeSpaceVolume.prod P) < ∞
  rw [lintegral_prod _ (hm'.pow_const 2).ennreal_ofReal.aemeasurable]
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono
  intro z
  change (∫⁻ ω, ENNReal.ofReal (G z.1 z.2 ω ^ 2) ∂P) ≤ _
  rw [hnorm]
  exact pow_le_pow_left' (eLpNorm_le_eLpNorm_of_exponent_le
    (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp))) 2

/-- Scaling inside `eLpNorm` and Tonelli expose the iterated deterministic
weight integral used by the deterministic weighted mixed norm. No finiteness is required. -/
theorem mixedNormSq_mul_deterministic {p : ℝ} (hp : 2 ≤ p)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (fun z : ℝ × ℝ => a z.1 z.2))
    (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)) :
    mixedNormSq P p (fun s y ω => a s y * G s y ω) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y : ℝ,
        ENNReal.ofReal (a s y ^ 2) * eLpNorm (G s y) (ENNReal.ofReal p) P ^ 2 := by
  have hnorm := measurable_sample_eLpNorm (P := P) (by linarith : 0 < p) hG
  unfold mixedNormSq
  have heq (z : ℝ × ℝ) :
      eLpNorm (fun ω => a z.1 z.2 * G z.1 z.2 ω) (ENNReal.ofReal p) P ^ 2 =
        ENNReal.ofReal (a z.1 z.2 ^ 2) * eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P ^ 2 := by
    rw [show (fun ω => a z.1 z.2 * G z.1 z.2 ω) = a z.1 z.2 • G z.1 z.2 from rfl,
      eLpNorm_const_smul, mul_pow, ← ofReal_norm, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [heq]
  exact lintegral_prod _ ((ha.pow_const 2).ennreal_ofReal.mul (hnorm.pow_const 2)).aemeasurable

private theorem gaussian_lintegral {p : ℝ} (hp : 0 < p) (v : ℝ≥0) :
    (∫⁻ x : ℝ, ‖x‖ₑ ^ p ∂gaussianReal 0 v) =
      ENNReal.ofReal (gaussianMoment p) ^ p * (v : ℝ≥0∞) ^ (p / 2) := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    convert gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v) using 1
    simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hm, lintegral_map (by fun_prop) (by fun_prop)]
  simp_rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hmoment : (∫⁻ x : ℝ, ‖x‖ₑ ^ p ∂gaussianReal 0 1) =
      ENNReal.ofReal (gaussianMoment p) ^ p := by
    rw [ofReal_gaussianMoment_eq_eLpNorm hp,
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
        (by fun_prop), ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
    simp [hp.ne']
  rw [hmoment, mul_comm]
  congr 1
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg v.coe_nonneg (by norm_num), ← ENNReal.rpow_mul]
  simp [div_eq_mul_inv, mul_comm]
private theorem slab_gram {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0) (hst : s < t)
    (hdisj : Pairwise (fun i j => Disjoint (e i).A (e j).A)) (a : Fin n → ℝ) :
    ‖∑ j, a j • rectangle s t (e j).A (e j).measurableSet_A (e j).volume_A_ne_top‖ ^ 2 =
      ((t : ℝ) - (s : ℝ)) * ∑ j, (volume (e j).A).toReal * a j ^ 2 := by
  classical
  have hfin (j : Fin n) : timeSpaceVolume (Ioc (s : ℝ) (t : ℝ) ×ˢ (e j).A) ≠ ∞ := by
    rw [timeSpaceVolume, Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (ne_of_lt ((Measure.restrict_apply_le _ _).trans_lt (by simp))) (e j).volume_A_ne_top
  have hinner (i j : Fin n) : inner ℝ
      (rectangle s t (e i).A (e i).measurableSet_A (e i).volume_A_ne_top)
      (rectangle s t (e j).A (e j).measurableSet_A (e j).volume_A_ne_top) =
      if i = j then ((t : ℝ) - (s : ℝ)) * (volume (e i).A).toReal else 0 := by
    unfold rectangle
    rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _ (hfin i) (hfin j)]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, inter_self, Measure.real, timeSpaceVolume, Measure.prod_prod,
        ENNReal.toReal_mul, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi,
        max_eq_left s.coe_nonneg, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst.le))]
    · simp [hij, prod_inter_prod, Disjoint.inter_eq (hdisj hij), Measure.real]
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hinner,
    conj_trivial, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Gaussian slab estimate, the moment identity obtained from the conditional Gaussian law.
Whole-future independence in `hW` and pairwise disjoint cells are essential.
The common endpoints are explicit; no disjointness in sample space is needed. -/
theorem eLpNorm_slab_sq_eq (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0) (hst : s < t)
    (hs : ∀ j, (e j).s = s) (ht : ∀ j, (e j).t = t)
    (hdisj : Pairwise (fun i j => Disjoint (e i).A (e j).A)) :
    eLpNorm (elementarySumIntegral W e) (ENNReal.ofReal p) P ^ 2 =
      ENNReal.ofReal (gaussianMoment p ^ 2) *
        eLpNorm (slabVariance s t e) (ENNReal.ofReal (p / 2)) P := by
  classical
  let r (j : Fin n) := rectangle s t (e j).A (e j).measurableSet_A (e j).volume_A_ne_top
  let C : Ω → Fin n → ℝ := fun ω j => (e j).coeff ω
  let Z : Ω → Fin n → ℝ := fun ω j => W (r j) ω
  let V : (Fin n → ℝ) → ℝ := fun a =>
    ((t : ℝ) - (s : ℝ)) * ∑ j, (volume (e j).A).toReal * a j ^ 2
  have hdt : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst.le)
  have hV (a : Fin n → ℝ) : 0 ≤ V a :=
    mul_nonneg hdt (Finset.sum_nonneg fun j _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  have hmV : Measurable V := by fun_prop
  have hC : Measurable[F s] C := by
    apply @Measurable.of_eval Ω (Fin n) (fun _ => ℝ) (F s) _ C
    intro j
    have hj := (e j).measurable_coeff
    rw [hs j] at hj
    exact hj
  have hC' := hC.mono (F.le s) le_rfl
  have hZ : Measurable Z := Measurable.of_eval (fun j => (Lp.stronglyMeasurable (W (r j))).measurable)
  have hind : IndepFun C Z P :=
    (indep_of_indep_of_le (hW.future_fin_indep s r
      (fun j => rectangle_supportedAfter s t _ _ _)) le_rfl hC.comap_le).symm
  have hp0 : 0 < p := by linarith
  have hfixed (a : Fin n → ℝ) :
      (∫⁻ z : Fin n → ℝ, ‖∑ j, a j * z j‖ₑ ^ p ∂P.map Z) =
        ENNReal.ofReal (gaussianMoment p) ^ p * ENNReal.ofReal (V a) ^ (p / 2) := by
    rw [lintegral_map (by fun_prop) hZ]
    have hlaw := hW.linear_combination_law r a
    have heq := lintegral_map (μ := P) (f := fun x : ℝ => ‖x‖ₑ ^ p)
      (g := fun ω => ∑ j, a j * W (r j) ω) (by fun_prop) (by fun_prop)
    rw [hlaw, gaussian_lintegral hp0] at heq
    rw [← heq]
    congr 2
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simpa only [NNReal.coe_pow, coe_nnnorm, r, V] using slab_gram e s t hst hdisj a
  have hmPair : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      ‖∑ j, q.1 j * q.2 j‖ₑ ^ p) := by fun_prop
  have hmSum : Measurable (fun ω => ∑ j, C ω j * Z ω j) := by fun_prop
  have hmVar : Measurable (slabVariance s t e) := hmV.comp hC'
  have hmoment : (∫⁻ ω, ‖∑ j, C ω j * Z ω j‖ₑ ^ p ∂P) =
      ENNReal.ofReal (gaussianMoment p) ^ p *
        ∫⁻ ω, ENNReal.ofReal (slabVariance s t e ω) ^ (p / 2) ∂P := by
    calc
      _ = ∫⁻ q : (Fin n → ℝ) × (Fin n → ℝ), ‖∑ j, q.1 j * q.2 j‖ₑ ^ p
          ∂P.map (fun ω => (C ω, Z ω)) := (lintegral_map hmPair (hC'.prodMk hZ)).symm
      _ = ∫⁻ a : Fin n → ℝ, ∫⁻ z : Fin n → ℝ, ‖∑ j, a j * z j‖ₑ ^ p
          ∂P.map Z ∂P.map C := by
        rw [hind.map_prod_eq_prod_map_map hC'.aemeasurable hZ.aemeasurable,
          lintegral_prod _ hmPair.aemeasurable]
      _ = _ := by
        simp_rw [hfixed]
        rw [lintegral_const_mul _ (hmV.ennreal_ofReal.pow_const _),
          lintegral_map (hmV.ennreal_ofReal.pow_const _) hC']
        rfl
  have hae : elementarySumIntegral W e =ᵐ[P] (fun ω => ∑ j, C ω j * Z ω j) := by
    filter_upwards [ae_all_iff.mpr (fun j => elementaryIntegral_ae W (e j))] with ω hω
    apply Finset.sum_congr rfl
    intro j _
    simpa only [C, Z, r, hs j, ht j] using hω j
  rw [eLpNorm_congr_ae hae]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hmSum.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le, hmoment]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hmVar.aestronglyMeasurable, ENNReal.toReal_ofReal (by positivity : 0 ≤ p / 2)]
  have hvnorm (ω : Ω) : ‖slabVariance s t e ω‖ₑ = ENNReal.ofReal (slabVariance s t e ω) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ slabVariance s t e ω from hV (C ω))]
  simp_rw [hvnorm]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  have hcancel : p * (1 / p * (2 : ℕ)) = 2 := by field_simp; norm_num
  have hcancel' : 1 / p * (2 : ℕ) = 1 / (p / 2) := by ring
  rw [hcancel, hcancel', ENNReal.rpow_two,
    ENNReal.ofReal_pow (le_of_lt (gaussianMoment_pos hp0))]

/-- The disjoint-cell slab bound: m_p² times the slab duration times the sum
of cell volumes weighted by squared coefficient L^p norms. -/
theorem eLpNorm_slab_sq_le (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0) (hst : s < t)
    (hs : ∀ j, (e j).s = s) (ht : ∀ j, (e j).t = t)
    (hdisj : Pairwise (fun i j => Disjoint (e i).A (e j).A)) :
    eLpNorm (elementarySumIntegral W e) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (gaussianMoment p ^ 2) * ENNReal.ofReal ((t : ℝ) - (s : ℝ)) *
        ∑ j, volume (e j).A * eLpNorm (e j).coeff (ENNReal.ofReal p) P ^ 2 := by
  rw [eLpNorm_slab_sq_eq hW hp e s t hst hs ht hdisj]
  have hdt : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst.le)
  have hexp : ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hcoeff (j : Fin n) :
      eLpNorm (fun ω => (e j).coeff ω ^ 2) (ENNReal.ofReal (p / 2)) P =
        eLpNorm (e j).coeff (ENNReal.ofReal p) P ^ 2 := by
    have h := eLpNorm_norm_rpow (p := ENNReal.ofReal (p / 2)) (e j).coeff
      ((e j).measurable_coeff.mono (F.le _) le_rfl).aestronglyMeasurable
      (by norm_num : (0 : ℝ) < 2) (μ := P)
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, hexp, ENNReal.rpow_two] using h
  have hvol (j : Fin n) : ‖(volume (e j).A).toReal‖ₑ = volume (e j).A := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (e j).volume_A_ne_top]
  have hdt' : ‖((t : ℝ) - (s : ℝ))‖ₑ = ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hdt]
  unfold slabVariance
  rw [show (fun ω => ((t : ℝ) - (s : ℝ)) *
      ∑ j, (volume (e j).A).toReal * (e j).coeff ω ^ 2) =
      ((t : ℝ) - (s : ℝ)) •
        (∑ j : Fin n, fun ω => (volume (e j).A).toReal * (e j).coeff ω ^ 2) by
    ext ω
    simp]
  rw [eLpNorm_const_smul, hdt', ← mul_assoc]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  calc
    eLpNorm (∑ j : Fin n, fun ω => (volume (e j).A).toReal * (e j).coeff ω ^ 2)
        (ENNReal.ofReal (p / 2)) P ≤
        ∑ j : Fin n, eLpNorm (fun ω => (volume (e j).A).toReal * (e j).coeff ω ^ 2)
          (ENNReal.ofReal (p / 2)) P :=
      eLpNorm_sum_le (by rw [ENNReal.one_le_ofReal]; linarith)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      change eLpNorm ((volume (e j).A).toReal • (fun ω => (e j).coeff ω ^ 2)) _ _ = _
      rw [eLpNorm_const_smul, hvol, hcoeff]

private theorem elementaryIntegral_memLp_real (hW : IsWhiteNoise P F W)
    (p : ℝ) (e : Elementary F) :
    MemLp (fun ω => elementaryIntegral W e ω) (ENNReal.ofReal p) P := by
  let r := rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top
  have hlaw : HasLaw (fun ω => W r ω) (gaussianReal 0 (‖r‖₊ ^ 2)) P :=
    ⟨(Lp.stronglyMeasurable (W r)).measurable.aemeasurable, hW.gaussian r⟩
  have hnoise := hlaw.memLp (memLp_id_gaussianReal' (ENNReal.ofReal p) ENNReal.ofReal_ne_top)
  obtain ⟨C, hC⟩ := e.bounded_coeff
  have hcoeff := memLp_top_of_bound (μ := P)
    (e.measurable_coeff.mono (F.le e.s) le_rfl).aestronglyMeasurable C (Eventually.of_forall hC)
  exact (hcoeff.mul hnoise).ae_eq (elementaryIntegral_ae W e).symm

private theorem elementaryIntegral_condExp_zero (hW : IsWhiteNoise P F W)
    (e : Elementary F) :
    P[(fun ω => elementaryIntegral W e ω) | F e.s] =ᵐ[P] (0 : Ω → ℝ) := by
  let r := rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top
  let Z : Ω → ℝ := fun ω => W r ω
  have hZ : Measurable Z := (Lp.stronglyMeasurable (W r)).measurable
  have hZm : StronglyMeasurable[MeasurableSpace.comap Z inferInstance] Z := by
    let : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance
    exact (show Measurable Z from measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hind := hW.future_indep e.s r (rectangle_supportedAfter _ _ _ _ _)
  have hc := condExp_indep_eq hZ.comap_le (F.le e.s) hZm hind
  have hlaw : HasLaw Z (gaussianReal 0 (‖r‖₊ ^ 2)) P :=
    ⟨hZ.aemeasurable, hW.gaussian r⟩
  have hz : ∫ ω, Z ω ∂P = 0 := hlaw.integral_eq.trans integral_id_gaussianReal
  have hprod := condExp_mul_of_stronglyMeasurable_left e.measurable_coeff.stronglyMeasurable
    ((elementaryIntegral_memLp W e).integrable (by norm_num))
    ((Lp.memLp (W r)).integrable (by norm_num))
  apply (condExp_congr_ae (elementaryIntegral_ae W e)).trans
  filter_upwards [hprod, hc] with ω hω hωc
  change P[fun ω => e.coeff ω * Z ω | F e.s] ω = 0
  have heq : (e.coeff * Z) = (fun ω => e.coeff ω * Z ω) := by ext ω; simp
  change P[e.coeff * Z | F e.s] ω = e.coeff ω * P[Z | F e.s] ω at hω
  rw [heq] at hω
  rw [hω, hωc, hz, mul_zero]

private theorem exists_elementaryIntegral_adapted_rep (hW : IsWhiteNoise P F W)
    (p : ℝ) (e : Elementary F) :
    ∃ D : Ω → ℝ, StronglyMeasurable[F e.t] D ∧
      D =ᵐ[P] (fun ω => elementaryIntegral W e ω) ∧
      MemLp D (ENNReal.ofReal p) P ∧ P[D | F e.s] =ᵐ[P] (0 : Ω → ℝ) := by
  obtain ⟨Z, hZ, hZae⟩ := hW.exists_stronglyMeasurable_rep e.t
    (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top)
    (rectangle_supportedBefore _ _ _ _ _)
  have hD : StronglyMeasurable[F e.t] (fun ω => e.coeff ω * Z ω) :=
    (e.measurable_coeff.stronglyMeasurable.mono (F.mono e.s_lt_t.le)).mul hZ
  have hae : (fun ω => e.coeff ω * Z ω) =ᵐ[P] (fun ω => elementaryIntegral W e ω) := by
    filter_upwards [hZae, elementaryIntegral_ae W e] with ω hω he
    rw [hω, he]
  exact ⟨_, hD, hae, (elementaryIntegral_memLp_real hW p e).ae_eq hae.symm,
    (condExp_congr_ae hae).trans (elementaryIntegral_condExp_zero hW e)⟩
private theorem exists_slab_adapted_rep (hW : IsWhiteNoise P F W)
    {p : ℝ} (hp : 2 ≤ p) {n : ℕ} (e : Fin n → Elementary F) (s t : ℝ≥0)
    (hs : ∀ j, (e j).s = s) (ht : ∀ j, (e j).t = t) :
    ∃ D : Ω → ℝ, StronglyMeasurable[F t] D ∧
      D =ᵐ[P] elementarySumIntegral W e ∧ MemLp D (ENNReal.ofReal p) P ∧
      P[D | F s] =ᵐ[P] (0 : Ω → ℝ) := by
  classical
  choose D hDm hDae hDLp hDc using fun j => exists_elementaryIntegral_adapted_rep hW p (e j)
  have hm : StronglyMeasurable[F t] (fun ω => ∑ j, D j ω) := by
    convert Finset.univ.stronglyMeasurable_sum (fun j _ => ht j ▸ hDm j) using 1
    ext ω
    simp
  have hae : (fun ω => ∑ j, D j ω) =ᵐ[P] elementarySumIntegral W e := by
    filter_upwards [ae_all_iff.mpr hDae] with ω hω
    exact Finset.sum_congr rfl (fun j _ => hω j)
  have hLp := memLp_finsetSum Finset.univ (fun j _ => hDLp j)
  refine ⟨_, hm, hae, hLp, ?_⟩
  have hc := condExp_finsetSum (s := Finset.univ)
    (fun j _ => (hDLp j).integrable (by rw [ENNReal.one_le_ofReal]; linarith)) (F s)
  have hfun : (∑ j, D j) = (fun ω => ∑ j, D j ω) := by ext ω; simp
  rw [hfun] at hc
  filter_upwards [hc, ae_all_iff.mpr (fun j => hs j ▸ hDc j)] with ω hω hωc
  simpa only [Finset.sum_apply, hωc, Pi.zero_apply, Finset.sum_const_zero] using hω

private theorem finite_spatial_refinement {n : ℕ} (A : Fin n → Set ℝ)
    (hA : ∀ j, MeasurableSet (A j)) (hfin : ∀ j, volume (A j) ≠ ∞) :
    ∃ (m : ℕ) (B : Fin m → Set ℝ) (I : Fin m → Finset (Fin n)),
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, volume (B i) ≠ ∞) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, (I i).Nonempty) ∧
      (∀ i y, y ∈ B i ↔ ∀ j, y ∈ A j ↔ j ∈ I i) ∧
      (∀ j, A j = ⋃ i : Fin m, if j ∈ I i then B i else ∅) := by
  classical
  let ι := {S : Finset (Fin n) // S.Nonempty}
  let C : ι → Set ℝ := fun S => ⋂ j : Fin n, if j ∈ S.val then A j else (A j)ᶜ
  have hmem (S : ι) (y : ℝ) : y ∈ C S ↔ ∀ j, y ∈ A j ↔ j ∈ S.val := by
    simp only [C, mem_iInter]
    constructor
    · intro hy j
      specialize hy j
      by_cases hj : j ∈ S.val <;> simpa [hj] using hy
    · intro hy j
      by_cases hj : j ∈ S.val <;> simp [hj, hy j]
  have hm (S : ι) : MeasurableSet (C S) := by
    apply MeasurableSet.iInter
    intro j
    split_ifs
    · exact hA j
    · exact (hA j).compl
  have hCfin (S : ι) : volume (C S) ≠ ∞ := by
    obtain ⟨j, hj⟩ := S.property
    apply ne_of_lt
    exact (measure_mono (fun y hy => (hmem S y).mp hy j |>.mpr hj)).trans_lt (lt_top_iff_ne_top.mpr (hfin j))
  have hdisj : Pairwise (fun S T : ι => Disjoint (C S) (C T)) := by
    intro S T hST
    apply disjoint_left.mpr
    intro y hyS hyT
    apply hST
    apply Subtype.ext
    apply Finset.ext
    intro j
    exact ((hmem S y).mp hyS j).symm.trans ((hmem T y).mp hyT j)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => C (e.symm i), fun i => (e.symm i).val,
    fun i => hm _, fun i => hCfin _, ?_, fun i => (e.symm i).property,
    fun i y => hmem _ y, ?_⟩
  · intro i j hij
    exact hdisj (e.symm.injective.ne hij)
  · intro j
    ext y
    constructor
    · intro hy
      let S : Finset (Fin n) := Finset.univ.filter (fun k => y ∈ A k)
      have hjS : j ∈ S := by simp [S, hy]
      let T : ι := ⟨S, ⟨j, hjS⟩⟩
      apply mem_iUnion.mpr
      refine ⟨e T, ?_⟩
      simp only [Equiv.symm_apply_apply, T, hjS, ite_true]
      apply (hmem T y).mpr
      intro k
      simp [T, S]
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      split_ifs at hi with hj
      · exact ((hmem _ y).mp hi j).mpr hj
      · exact False.elim (notMem_empty y hi)

section Refinement

open scoped Classical

private theorem finite_time_grid {n : ℕ} (e : Fin n → Elementary F) :
    ∃ (m : ℕ) (τ : ℕ → ℝ≥0), Monotone τ ∧ τ 0 = 0 ∧
      (∀ k, k < m → τ k < τ (k + 1)) ∧
      (∀ j, ∃ i ≤ m, τ i = (e j).s) ∧
      (∀ j, ∃ i ≤ m, τ i = (e j).t) := by
  classical
  let S := insert 0 ((Finset.univ.image fun j => (e j).s) ∪
    (Finset.univ.image fun j => (e j).t))
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let f : Fin (m + 1) ↪o ℝ≥0 := S.orderEmbOfFin hm
  let τ : ℕ → ℝ≥0 := fun k => f ⟨min k m, by omega⟩
  have hmono : Monotone τ := fun i j hij => f.monotone (by
    change min i m ≤ min j m
    exact min_le_min_right m hij)
  have hsurj (x : ℝ≥0) (hx : x ∈ S) : ∃ i ≤ m, τ i = x := by
    obtain ⟨i, hi⟩ := (show x ∈ Set.range f by
      rw [Finset.range_orderEmbOfFin]; exact hx)
    refine ⟨i.val, by omega, ?_⟩
    simpa [τ, Nat.min_eq_left (show i.val ≤ m by omega)] using hi
  refine ⟨m, τ, hmono, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi, he⟩ := hsurj 0 (Finset.mem_insert_self _ _)
    exact le_antisymm (he ▸ hmono (Nat.zero_le i)) zero_le
  · intro k hk
    apply f.strictMono
    change min k m < min (k + 1) m
    omega
  · intro j
    exact hsurj _ (by simp [S])
  · intro j
    exact hsurj _ (by simp [S])

private theorem grid_slab_membership (τ : ℕ → ℝ≥0) (hmono : Monotone τ)
    (s t : ℝ≥0) (hs : ∃ i, τ i = s) (ht : ∃ i, τ i = t)
    (k : ℕ) {r : ℝ} (hr : r ∈ Ioc (τ k : ℝ) (τ (k + 1) : ℝ)) :
    r ∈ Ioc (s : ℝ) (t : ℝ) ↔ s ≤ τ k ∧ τ (k + 1) ≤ t := by
  obtain ⟨i, rfl⟩ := hs
  obtain ⟨j, rfl⟩ := ht
  constructor
  · intro h
    constructor
    · have hik : i ≤ k := by
        by_contra hle
        have hm := hmono (show k + 1 ≤ i by omega)
        have hm' : (τ (k + 1) : ℝ) ≤ τ i := hm
        exact (not_lt_of_ge (hr.2.trans hm')) h.1
      exact hmono hik
    · have hkj : k + 1 ≤ j := by
        by_contra hle
        have hm := hmono (show j ≤ k by omega)
        have hm' : (τ j : ℝ) ≤ τ k := hm
        exact (not_lt_of_ge (h.2.trans hm')) hr.1
      exact hmono hkj
  · rintro ⟨h₁, h₂⟩
    exact ⟨lt_of_le_of_lt (show (τ i : ℝ) ≤ τ k from h₁) hr.1,
      le_trans hr.2 (show (τ (k + 1) : ℝ) ≤ τ j from h₂)⟩

private theorem grid_slab_disjoint (τ : ℕ → ℝ≥0) (hmono : Monotone τ) :
    Pairwise (fun i j : ℕ => Disjoint (Ioc (τ i : ℝ) (τ (i + 1) : ℝ))
      (Ioc (τ j : ℝ) (τ (j + 1) : ℝ))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro r hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hm : (τ (i + 1) : ℝ) ≤ τ j := hmono (by omega)
    exact (not_lt_of_ge (hi.2.trans hm)) hj.1
  · have hm : (τ (j + 1) : ℝ) ≤ τ i := hmono (by omega)
    exact (not_lt_of_ge (hj.2.trans hm)) hi.1


private theorem grid_slab_cover (m : ℕ) (τ : ℕ → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0 = 0) (s t : ℝ≥0) (ht : ∃ i ≤ m, τ i = t)
    {r : ℝ} (hr : r ∈ Ioc (s : ℝ) (t : ℝ)) :
    ∃ k : Fin m, r ∈ Ioc (τ k : ℝ) (τ (k + 1) : ℝ) := by
  obtain ⟨i, hi, rfl⟩ := ht
  have hr' : r ∈ Ioc (τ 0 : ℝ) (τ m : ℝ) :=
    ⟨by simpa [hzero] using lt_of_le_of_lt s.coe_nonneg hr.1,
      hr.2.trans (show (τ i : ℝ) ≤ τ m from hmono hi)⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (Ioc_subset_biUnion_Ioc m (fun i => (τ i : ℝ)) hr')
  obtain ⟨hk, hrk⟩ := mem_iUnion.mp hk
  exact ⟨⟨k, Finset.mem_range.mp hk⟩, hrk⟩

private theorem sum_integral_congr_field (hW : IsWhiteNoise P F W)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Elementary F) (f : κ → Elementary F)
    (h : ∀ s y ω, ∑ i, (e i).field s y ω = ∑ j, (f j).field s y ω) :
    (fun ω => ∑ i, elementaryIntegral W (e i) ω) =ᵐ[P]
      (fun ω => ∑ j, elementaryIntegral W (f j) ω) := by
  classical
  have hc : (∑ i, elementaryClass P (e i)) = ∑ j, elementaryClass P (f j) := by
    apply Subtype.ext
    apply Lp.ext
    have he := Lp.coeFn_finsetSum Finset.univ (fun i => (elementaryClass P (e i)).val)
    have hf := Lp.coeFn_finsetSum Finset.univ (fun i => (elementaryClass P (f i)).val)
    filter_upwards [he, hf,
      ae_all_iff.mpr (fun i => toPredL2_ae (e i).field (e i).inDomain),
      ae_all_iff.mpr (fun i => toPredL2_ae (f i).field (f i).inDomain)] with q hqe hqf heq hfq
    simp only [Submodule.coe_sum, hqe, hqf, Finset.sum_apply]
    change (∑ i, (toPredL2 (e i).field (e i).inDomain).val q) =
      ∑ j, (toPredL2 (f j).field (f j).inDomain).val q
    simpa only [heq, hfq] using h q.1 q.2.1 q.2.2
  have hi : (∑ i, elementaryIntegral W (e i)) = ∑ j, elementaryIntegral W (f j) := by
    simpa only [map_sum, walshL2_elementary] using congrArg (walshL2 hW) hc
  have hae :=
    (Lp.coeFn_finsetSum Finset.univ (fun i => elementaryIntegral W (e i))).symm.trans
      (hi ▸ Lp.coeFn_finsetSum Finset.univ (fun i => elementaryIntegral W (f i)))
  filter_upwards [hae] with ω hω
  simpa only [Finset.sum_apply] using hω

private theorem spatial_regroup {n r : ℕ} (A : Fin n → Set ℝ)
    (B : Fin r → Set ℝ) (I : Fin r → Finset (Fin n))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hmem : ∀ j y, y ∈ B j ↔ ∀ i, y ∈ A i ↔ i ∈ I j)
    (hcover : ∀ i, A i = ⋃ j : Fin r, if i ∈ I j then B j else ∅)
    (a : Fin n → ℝ) (y : ℝ) :
    (∑ j, if y ∈ B j then ∑ i ∈ I j, a i else 0) =
      ∑ i, if y ∈ A i then a i else 0 := by
  classical
  by_cases hy : ∃ j, y ∈ B j
  · obtain ⟨j, hj⟩ := hy
    rw [Finset.sum_eq_single j]
    · simp only [hj, ite_true]
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp [(hmem j y).mp hj i]
    · intro k hk hkj
      have hn : y ∉ B k := fun h => (disjoint_left.mp (hdisj hkj)) h hj
      simp [hn]
    · simp
  · have hn (j) : y ∉ B j := fun hj => hy ⟨j, hj⟩
    have hA (i) : y ∉ A i := by
      rw [hcover i]
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      split_ifs at hj with hij
      · exact hn j hj
      · exact notMem_empty y hj
    simp [hn, hA]

private theorem exists_grid_refinement {n m : ℕ} (e : Fin n → Elementary F)
    (τ : ℕ → ℝ≥0) (hmono : Monotone τ)
    (hstrict : ∀ k, k < m → τ k < τ (k + 1))
    (hs : ∀ i, ∃ k, τ k = (e i).s) (ht : ∀ i, ∃ k, τ k = (e i).t) :
    ∃ (r : ℕ) (f : Fin m → Fin r → Elementary F),
      (∀ k j, (f k j).s = τ k) ∧ (∀ k j, (f k j).t = τ (k + 1)) ∧
      (∀ k, Pairwise (fun i j => Disjoint (f k i).A (f k j).A)) ∧
      (∀ k s y ω, elementarySum (f k) s y ω =
        if s ∈ Ioc (τ k : ℝ) (τ (k + 1) : ℝ) then elementarySum e s y ω else 0) := by
  classical
  obtain ⟨r, B, I, hB, hBfin, hd, hI, hmem, hcover⟩ :=
    finite_spatial_refinement (fun i => (e i).A)
      (fun i => (e i).measurableSet_A) (fun i => (e i).volume_A_ne_top)
  let active (k : Fin m) (i : Fin n) := (e i).s ≤ τ k ∧ τ (k + 1) ≤ (e i).t
  let c (k : Fin m) (j : Fin r) : Ω → ℝ := fun ω =>
    ∑ i ∈ I j, if active k i then (e i).coeff ω else 0
  have hc (k : Fin m) (j : Fin r) : Measurable[F (τ k)] (c k j) := by
    apply Finset.measurable_sum
    intro i hi
    by_cases hai : active k i
    · simpa [hai] using (e i).measurable_coeff.mono (F.mono hai.1) le_rfl
    · simp only [hai, ite_false]
      exact measurable_const
  choose C hC using fun i => (e i).bounded_coeff
  have hb (k : Fin m) (j : Fin r) : ∃ C : ℝ, ∀ ω, ‖c k j ω‖ ≤ C := by
    refine ⟨∑ i ∈ I j, |C i|, fun ω => ?_⟩
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    by_cases hai : active k i
    · simpa only [hai, ite_true] using (hC i ω).trans (le_abs_self _)
    · simp [hai]
  let f (k : Fin m) (j : Fin r) : Elementary F :=
    ⟨τ k, τ (k + 1), hstrict k k.isLt, B j, hB j, hBfin j, c k j, hc k j, hb k j⟩
  refine ⟨r, f, fun _ _ => rfl, fun _ _ => rfl, fun _ => hd, ?_⟩
  intro k s y ω
  by_cases hsk : s ∈ Ioc (τ k : ℝ) (τ (k + 1) : ℝ)
  · simp only [hsk, ite_true]
    have hfield : elementarySum (f k) s y ω =
        ∑ j, if y ∈ B j then ∑ i ∈ I j, if active k i then (e i).coeff ω else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hy : y ∈ B j <;> simp [Elementary.field, f, c, hsk, hy]
    rw [hfield, spatial_regroup _ B I hd hmem hcover]
    apply Finset.sum_congr rfl
    intro i _
    have htime := grid_slab_membership τ hmono (e i).s (e i).t (hs i) (ht i) k hsk
    change s ∈ Ioc ((e i).s : ℝ) ((e i).t : ℝ) ↔ active k i at htime
    simp only [Elementary.field, Set.indicator_apply, Set.mem_prod, htime]
    by_cases hy : y ∈ (e i).A <;> by_cases ha : active k i <;> simp [hy, ha]
  · simp only [hsk, ite_false]
    apply Finset.sum_eq_zero
    intro j _
    simp [Elementary.field, f, hsk]


omit [IsProbabilityMeasure P] in
private theorem mixedNormSq_disjoint {ι : Type*} [Fintype ι]
    (p : ℝ) (e : ι → Elementary F)
    (hd : Pairwise (fun i j => Disjoint
      (Ioc ((e i).s : ℝ) ((e i).t : ℝ) ×ˢ (e i).A)
      (Ioc ((e j).s : ℝ) ((e j).t : ℝ) ×ˢ (e j).A))) :
    mixedNormSq P p (fun s y ω => ∑ i, (e i).field s y ω) =
      ∑ i, ENNReal.ofReal ((e i).t - (e i).s : ℝ) * volume (e i).A *
        eLpNorm (e i).coeff (ENNReal.ofReal p) P ^ 2 := by
  classical
  let S (i : ι) := Ioc ((e i).s : ℝ) ((e i).t : ℝ) ×ˢ (e i).A
  have heq (z : ℝ × ℝ) :
      eLpNorm (fun ω => ∑ i, (e i).field z.1 z.2 ω) (ENNReal.ofReal p) P ^ 2 =
        ∑ i, (S i).indicator (fun _ => eLpNorm (e i).coeff (ENNReal.ofReal p) P ^ 2) z := by
    by_cases hz : ∃ i, z ∈ S i
    · obtain ⟨i, hi⟩ := hz
      have hn (j : ι) (hji : j ≠ i) : z ∉ S j := fun hj => disjoint_left.mp (hd hji) hj hi
      have hf : (fun ω => ∑ j, (e j).field z.1 z.2 ω) = (e i).coeff := by
        funext ω
        rw [Finset.sum_eq_single i]
        · change (e i).coeff ω * (S i).indicator (fun _ => (1 : ℝ)) z = _
          simp [hi]
        · intro j hj hji
          change (e j).coeff ω * (S j).indicator (fun _ => (1 : ℝ)) z = _
          simp [hn j hji]
        · simp
      rw [hf, Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        simp [hn j hji]
      · simp
    · have hn (i) : z ∉ S i := fun hi => hz ⟨i, hi⟩
      have hf : (fun ω => ∑ i, (e i).field z.1 z.2 ω) = 0 := by
        funext ω
        change (∑ i, (e i).coeff ω * (S i).indicator (fun _ => (1 : ℝ)) z) = 0
        simp [hn]
      simp [hf, hn]
  have hS (i) : MeasurableSet (S i) := measurableSet_Ioc.prod (e i).measurableSet_A
  have hvol (i) : timeSpaceVolume (S i) =
      ENNReal.ofReal ((e i).t - (e i).s : ℝ) * volume (e i).A := by
    rw [timeSpaceVolume, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc ((e i).s : ℝ) ((e i).t : ℝ) ⊆ Ioi (0 : ℝ) from
        fun z hz => lt_of_le_of_lt (e i).s.coe_nonneg hz.1), Real.volume_Ioc]
  unfold mixedNormSq
  simp_rw [heq]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hS i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator_const (hS i), hvol, mul_comm]


private theorem grid_refinement_field_sum {n m r : ℕ} (e : Fin n → Elementary F)
    (τ : ℕ → ℝ≥0) (hmono : Monotone τ) (hzero : τ 0 = 0)
    (ht : ∀ j, ∃ i ≤ m, τ i = (e j).t) (f : Fin m → Fin r → Elementary F)
    (hf : ∀ k s y ω, elementarySum (f k) s y ω =
      if s ∈ Ioc (τ k : ℝ) (τ (k + 1) : ℝ) then elementarySum e s y ω else 0) :
    ∀ s y ω, (∑ k, elementarySum (f k) s y ω) = elementarySum e s y ω := by
  classical
  intro s y ω
  by_cases hs : ∃ k : Fin m, s ∈ Ioc (τ k : ℝ) (τ (k + 1) : ℝ)
  · obtain ⟨k, hk⟩ := hs
    rw [Finset.sum_eq_single k, hf, ite_eq_left hk]
    · intro j hj hjk
      have hn : s ∉ Ioc (τ j : ℝ) (τ (j + 1) : ℝ) := fun h =>
        disjoint_left.mp (grid_slab_disjoint τ hmono (Fin.val_ne_of_ne hjk)) h hk
      simp [hf, hn]
    · simp
  · have hn (k : Fin m) : s ∉ Ioc (τ k : ℝ) (τ (k + 1) : ℝ) := fun h => hs ⟨k, h⟩
    simp only [hf, hn, ite_false, Finset.sum_const_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hi : s ∉ Ioc ((e i).s : ℝ) ((e i).t : ℝ) := fun h =>
      hs (grid_slab_cover m τ hmono hzero (e i).s (e i).t (ht i) h)
    simp [Elementary.field, hi]

private theorem grid_refinement_disjoint {m r : ℕ} (τ : ℕ → ℝ≥0) (hmono : Monotone τ)
    (f : Fin m → Fin r → Elementary F)
    (hs : ∀ k j, (f k j).s = τ k) (ht : ∀ k j, (f k j).t = τ (k + 1))
    (hd : ∀ k, Pairwise (fun i j => Disjoint (f k i).A (f k j).A)) :
    Pairwise (fun a b : Fin m × Fin r => Disjoint
      (Ioc ((f a.1 a.2).s : ℝ) ((f a.1 a.2).t : ℝ) ×ˢ (f a.1 a.2).A)
      (Ioc ((f b.1 b.2).s : ℝ) ((f b.1 b.2).t : ℝ) ×ˢ (f b.1 b.2).A)) := by
  intro a b hab
  apply disjoint_left.mpr
  rintro z ⟨hza, hya⟩ ⟨hzb, hyb⟩
  by_cases hk : a.1 = b.1
  · have hj : a.2 ≠ b.2 := fun h => hab (Prod.ext hk h)
    rw [← hk] at hyb
    exact disjoint_left.mp (hd a.1 hj) hya hyb
  · simp only [hs, ht] at hza hzb
    exact disjoint_left.mp (grid_slab_disjoint τ hmono (Fin.val_ne_of_ne hk)) hza hzb

private theorem grid_rio_bound (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    {m r : ℕ} (τ : ℕ → ℝ≥0) (hmono : Monotone τ)
    (f : Fin m → Fin r → Elementary F)
    (hs : ∀ k j, (f k j).s = τ k) (ht : ∀ k j, (f k j).t = τ (k + 1)) :
    eLpNorm (fun ω => ∑ k, elementarySumIntegral W (f k) ω) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (p - 1) * ∑ k, eLpNorm (elementarySumIntegral W (f k)) (ENNReal.ofReal p) P ^ 2 := by
  classical
  choose D hDm hDae hDLp hDc using fun k =>
    exists_slab_adapted_rep hW hp (f k) (τ k) (τ (k + 1)) (hs k) (ht k)
  let ℱ : Filtration ℕ mΩ := ⟨fun k => F (τ k), F.mono'.comp hmono, fun k => F.le _⟩
  let d : ℕ → Ω → ℝ := fun k => if hk : k < m then D ⟨k, hk⟩ else 0
  have hadapted (k : ℕ) : StronglyMeasurable[ℱ (k + 1)] (d k) := by
    by_cases hk : k < m
    · simpa only [d, dite_eq_left hk] using hDm ⟨k, hk⟩
    · simp only [d, dite_eq_right hk]
      exact stronglyMeasurable_zero
  have hLp (k : ℕ) : MemLp (d k) (ENNReal.ofReal p) P := by
    by_cases hk : k < m
    · simpa only [d, dite_eq_left hk] using hDLp ⟨k, hk⟩
    · simp only [d, dite_eq_right hk]
      exact MemLp.zero
  have hc (k : ℕ) : P[d k | ℱ k] =ᵐ[P] (0 : Ω → ℝ) := by
    by_cases hk : k < m
    · simpa only [d, dite_eq_left hk] using hDc ⟨k, hk⟩
    · simp [d, hk]
  have hr := Rio.eLpNorm_sum_sq_le P ℱ hp d hadapted hLp hc m
  have heq : (fun ω => ∑ k ∈ Finset.range m, d k ω) =ᵐ[P]
      (fun ω => ∑ k, elementarySumIntegral W (f k) ω) := by
    filter_upwards [ae_all_iff.mpr hDae] with ω hω
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simpa only [d, dite_eq_left k.isLt] using hω k
  rw [eLpNorm_congr_ae heq] at hr
  convert hr using 1
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [d, dite_eq_left k.isLt, eLpNorm_congr_ae (hDae k)]


end Refinement

/-- the corresponding interface for arbitrary finite elementary sums. Refining to common time slabs and
disjoint spatial cells is a proof obligation, not a hypothesis on the caller. -/
theorem eLpNorm_elementarySumIntegral_sq_le (hW : IsWhiteNoise P F W)
    {p : ℝ} (hp : 2 ≤ p) {n : ℕ} (e : Fin n → Elementary F) :
    eLpNorm (elementarySumIntegral W e) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (bdgConst p) * mixedNormSq P p (elementarySum e) := by
  classical
  obtain ⟨m, τ, hmono, hzero, hstrict, hs, ht⟩ := finite_time_grid e
  obtain ⟨r, f, hfs, hft, hfd, hfield⟩ := exists_grid_refinement e τ hmono hstrict
    (fun i => (hs i).imp fun _ h => h.2) (fun i => (ht i).imp fun _ h => h.2)
  have hsum := grid_refinement_field_sum e τ hmono hzero ht f hfield
  have hflat (s y : ℝ) (ω : Ω) :
      (∑ a : Fin m × Fin r, (f a.1 a.2).field s y ω) = elementarySum e s y ω := by
    rw [Fintype.sum_prod_type]
    exact hsum s y ω
  have hint : elementarySumIntegral W e =ᵐ[P]
      (fun ω => ∑ k, elementarySumIntegral W (f k) ω) := by
    have h := sum_integral_congr_field hW e (fun a : Fin m × Fin r => f a.1 a.2)
      (fun s y ω => (hflat s y ω).symm)
    filter_upwards [h] with ω hω
    simpa only [Fintype.sum_prod_type, elementarySumIntegral] using hω
  have hbudget : mixedNormSq P p (elementarySum e) =
      ∑ k : Fin m, ENNReal.ofReal ((τ (k + 1) : ℝ) - τ k) *
        ∑ j, volume (f k j).A * eLpNorm (f k j).coeff (ENNReal.ofReal p) P ^ 2 := by
    calc
      _ = mixedNormSq P p (fun s y ω => ∑ a : Fin m × Fin r, (f a.1 a.2).field s y ω) := by
        congr 1
        funext s y ω
        exact (hflat s y ω).symm
      _ = _ := by
        rw [mixedNormSq_disjoint p _ (grid_refinement_disjoint τ hmono f hfs hft hfd),
          Fintype.sum_prod_type]
        simp only [hfs, hft, Finset.mul_sum, mul_assoc]
  rw [eLpNorm_congr_ae hint]
  calc
    _ ≤ ENNReal.ofReal (p - 1) *
        ∑ k, eLpNorm (elementarySumIntegral W (f k)) (ENNReal.ofReal p) P ^ 2 :=
      grid_rio_bound hW hp τ hmono f hfs hft
    _ ≤ ENNReal.ofReal (p - 1) *
        ∑ k : Fin m, ENNReal.ofReal (gaussianMoment p ^ 2) *
          ENNReal.ofReal ((τ (k + 1) : ℝ) - τ k) *
          ∑ j, volume (f k j).A * eLpNorm (f k j).coeff (ENNReal.ofReal p) P ^ 2 := by
      refine mul_le_mul le_rfl ?_ zero_le zero_le
      apply Finset.sum_le_sum
      intro k _
      exact eLpNorm_slab_sq_le hW hp (f k) (τ k) (τ (k + 1))
        (hstrict k k.isLt) (hfs k) (hft k) (hfd k)
    _ = _ := by
      rw [hbudget, bdgConst, ENNReal.ofReal_mul (by linarith : 0 ≤ p - 1)]
      simp only [Finset.mul_sum, mul_assoc]

private theorem bounded_box_inDomain (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (M T R : ℝ) (hbound : ∀ s y ω, |G s y ω| ≤ M)
    (hsupport : ∀ s y ω, (s, y) ∉ Ioc 0 T ×ˢ Icc (-R) R → G s y ω = 0) :
    InDomain F P G := by
  classical
  let D : Set (ℝ × ℝ × Ω) := Ioc 0 T ×ˢ (Icc (-R) R ×ˢ univ)
  have hD : MeasurableSet D := measurableSet_Ioc.prod (measurableSet_Icc.prod .univ)
  have hDfin : spaceTimeSample P D ≠ ∞ := by
    rw [spaceTimeSample, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one]
    apply ENNReal.mul_ne_top
    · exact ne_of_lt ((Measure.restrict_apply_le _ _).trans_lt (by simp))
    · simp
  have hLp : MemLp (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) 2
      (spaceTimeSample P) := by
    apply (memLp_indicator_const 2 hD.nullMeasurableSet M (Or.inr hDfin)).of_le
      (hG.mono (predictableSigma_le F) le_rfl).aestronglyMeasurable
    apply ae_of_all
    intro q
    by_cases hq : q ∈ D
    · simpa only [indicator_of_mem hq, Real.norm_eq_abs] using
        (hbound q.1 q.2.1 q.2.2).trans (le_abs_self M)
    · have hz := hsupport q.1 q.2.1 q.2.2 (by simpa [D] using hq)
      simp [hz, indicator_of_notMem hq]
  exact ⟨hG, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun _ => sq_nonneg _)).mp hLp.integrable_sq.2⟩

private theorem elementary_rescale (c : ℝ) (e : Elementary F) :
    ∃ d : Elementary F, elementaryClass P d = c • elementaryClass P e := by
  let d : Elementary F := { e with
    coeff := fun ω => c * e.coeff ω
    measurable_coeff := measurable_const.mul e.measurable_coeff
    bounded_coeff := by
      obtain ⟨C, hC⟩ := e.bounded_coeff
      exact ⟨|c| * C, fun ω => by
        simpa only [norm_mul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩ }
  refine ⟨d, ?_⟩
  have hd : d.field = fun s y ω => c * e.field s y ω := by
    funext s y ω
    exact mul_assoc _ _ _
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [toPredL2_ae d.field d.inDomain,
    toPredL2_ae e.field e.inDomain,
    Lp.coeFn_smul c (elementaryClass P e).val] with q hq he hc
  change (toPredL2 d.field d.inDomain).val q =
    (c • (elementaryClass P e).val) q
  rw [hq, hc]
  change d.field q.1 q.2.1 q.2.2 = c * (toPredL2 e.field e.inDomain).val q
  rw [he, hd]

private theorem span_exists_elementarySum (x : PredL2 F P)
    (hx : x ∈ Submodule.span ℝ (range (elementaryClass (F := F) P))) :
    ∃ (n : ℕ) (e : Fin n → Elementary F), x = ∑ i, elementaryClass P (e i) := by
  classical
  rw [← Finsupp.range_linearCombination, LinearMap.mem_range] at hx
  obtain ⟨c, rfl⟩ := hx
  choose d hd using fun e : Elementary F => elementary_rescale (P := P) (c e) e
  let eqv := Fintype.equivFin c.support
  refine ⟨Fintype.card c.support, fun i => d (eqv.symm i).val, ?_⟩
  simp only [hd, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [← Finset.sum_coe_sort]
  exact (eqv.symm.sum_comp (fun e : c.support => c e.val • elementaryClass P e.val)).symm

private theorem exists_elementarySum_tendsto_ae (G : ℝ → ℝ → Ω → ℝ)
    (hG : InDomain F P G) :
    ∃ (N : ℕ → ℕ) (e : (k : ℕ) → Fin (N k) → Elementary F),
      ∀ᵐ q ∂spaceTimeSample P,
        Tendsto (fun k => elementarySum (e k) q.1 q.2.1 q.2.2) atTop
          (𝓝 (G q.1 q.2.1 q.2.2)) := by
  classical
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp
    (dense_elementary (F := F) (P := P) (toPredL2 G hG))
  choose N e he using fun k => span_exists_elementarySum (x k) (hx k)
  have hval : Tendsto (fun k => (x k).val) atTop (𝓝 (toPredL2 G hG).val) :=
    continuous_subtype_val.tendsto _ |>.comp hlim
  have hae (k : ℕ) : (fun q => (x k).val q) =ᵐ[spaceTimeSample P]
      (fun q => elementarySum (e k) q.1 q.2.1 q.2.2) := by
    rw [he k]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => (elementaryClass P (e k i)).val),
      ae_all_iff.mpr (fun i => toPredL2_ae (e k i).field (e k i).inDomain)]
      with q hq hi
    simp only [Submodule.coe_sum, hq, Finset.sum_apply]
    change (∑ i, (toPredL2 (e k i).field (e k i).inDomain).val q) = _
    simp only [hi, elementarySum]
  have hmeasure := (tendstoInMeasure_of_tendsto_Lp hval).congr
    hae (toPredL2_ae G hG)
  obtain ⟨ns, _, hns⟩ := hmeasure.exists_seq_tendsto_ae
  exact ⟨fun k => N (ns k), fun k => e (ns k), hns⟩

private theorem elementary_restrict_box (e : Elementary F) (T R : ℝ) (hT : 0 < T) :
    ∃ d : Elementary F, ∀ s y ω, d.field s y ω =
      if (s, y) ∈ Ioc 0 T ×ˢ Icc (-R) R then e.field s y ω else 0 := by
  classical
  let t : ℝ≥0 := min e.t ⟨T, hT.le⟩
  by_cases ht : e.s < t
  · let d : Elementary F := { e with
      t := t
      s_lt_t := ht
      A := e.A ∩ Icc (-R) R
      measurableSet_A := e.measurableSet_A.inter measurableSet_Icc
      volume_A_ne_top := ne_of_lt ((measure_mono inter_subset_left).trans_lt
        (lt_top_iff_ne_top.mpr e.volume_A_ne_top)) }
    refine ⟨d, fun s y ω => ?_⟩
    have htime : s ∈ Ioc (e.s : ℝ) (t : ℝ) ↔
        s ∈ Ioc (e.s : ℝ) (e.t : ℝ) ∧ s ∈ Ioc 0 T := by
      change ((e.s : ℝ) < s ∧ s ≤ min (e.t : ℝ) T) ↔ _
      simp only [mem_Ioc, le_min_iff]
      constructor
      · rintro ⟨hs, he, hT⟩
        exact ⟨⟨hs, he⟩, lt_of_le_of_lt e.s.coe_nonneg hs, hT⟩
      · tauto
    simp only [Elementary.field, d, mem_prod, mem_inter_iff, htime, indicator_apply]
    split_ifs <;> simp_all
  · let d : Elementary F := { e with
      coeff := fun _ => 0
      measurable_coeff := measurable_const
      bounded_coeff := ⟨0, fun _ => by simp⟩ }
    refine ⟨d, fun s y ω => ?_⟩
    have hno : ¬ (s ∈ Ioc (e.s : ℝ) (e.t : ℝ) ∧ s ∈ Ioc 0 T) := by
      rintro ⟨hs, hbox⟩
      apply ht
      change (e.s : ℝ) < min (e.t : ℝ) T
      exact lt_min (hs.1.trans_le hs.2) (hs.1.trans_le hbox.2)
    simp only [Elementary.field, d, zero_mul]
    split_ifs with hbox
    · have hn : s ∉ Ioc (e.s : ℝ) (e.t : ℝ) := fun hs => hno ⟨hs, hbox.1⟩
      simp [hn]
    · rfl

private theorem disjoint_elementary_clip {ι : Type*} [Fintype ι]
    (e : ι → Elementary F) (M : ℝ) (hM : 0 ≤ M)
    (hd : Pairwise (fun i j => Disjoint
      (Ioc ((e i).s : ℝ) ((e i).t : ℝ) ×ˢ (e i).A)
      (Ioc ((e j).s : ℝ) ((e j).t : ℝ) ×ˢ (e j).A))) :
    ∃ d : ι → Elementary F, ∀ s y ω,
      (∑ i, (d i).field s y ω) = max (-M) (min M (∑ i, (e i).field s y ω)) := by
  classical
  let d (i : ι) : Elementary F := { e i with
    coeff := fun ω => max (-M) (min M ((e i).coeff ω))
    measurable_coeff := measurable_const.max (measurable_const.min (e i).measurable_coeff)
    bounded_coeff := ⟨M, fun ω => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩ }
  refine ⟨d, fun s y ω => ?_⟩
  by_cases hz : ∃ i, (s, y) ∈ Ioc ((e i).s : ℝ) ((e i).t : ℝ) ×ˢ (e i).A
  · obtain ⟨i, hi⟩ := hz
    have hn (j : ι) (hji : j ≠ i) :
        (s, y) ∉ Ioc ((e j).s : ℝ) ((e j).t : ℝ) ×ˢ (e j).A :=
      fun hj => disjoint_left.mp (hd hji) hj hi
    have he : (∑ j, (e j).field s y ω) = (e i).coeff ω := by
      rw [Finset.sum_eq_single i]
      · simp [Elementary.field, hi]
      · intro j _ hji
        simp [Elementary.field, hn j hji]
      · simp
    have hd' : (∑ j, (d j).field s y ω) = max (-M) (min M ((e i).coeff ω)) := by
      rw [Finset.sum_eq_single i]
      · simp [Elementary.field, d, hi]
      · intro j _ hji
        simp [Elementary.field, d, hn j hji]
      · simp
    rw [he, hd']
  · have hn (i : ι) :
        (s, y) ∉ Ioc ((e i).s : ℝ) ((e i).t : ℝ) ×ˢ (e i).A := fun hi => hz ⟨i, hi⟩
    simp [Elementary.field, d, hn, min_eq_right hM, max_eq_right (neg_nonpos.mpr hM)]

private theorem exists_elementary_clip_box {n : ℕ} (e : Fin n → Elementary F)
    (M T R : ℝ) (hM : 0 ≤ M) (hT : 0 < T) :
    ∃ (l : ℕ) (d : Fin l → Elementary F), ∀ s y ω,
      elementarySum d s y ω = if (s, y) ∈ Ioc 0 T ×ˢ Icc (-R) R then
        max (-M) (min M (elementarySum e s y ω)) else 0 := by
  classical
  choose b hb using fun i => elementary_restrict_box (e i) T R hT
  have hbox (s y : ℝ) (ω : Ω) : elementarySum b s y ω =
      if (s, y) ∈ Ioc 0 T ×ˢ Icc (-R) R then elementarySum e s y ω else 0 := by
    simp only [elementarySum, hb]
    split_ifs <;> simp
  obtain ⟨m, τ, hmono, hzero, hstrict, hs, ht⟩ := finite_time_grid b
  obtain ⟨r, f, hfs, hft, hfd, hfield⟩ := exists_grid_refinement b τ hmono hstrict
    (fun i => (hs i).imp fun _ h => h.2) (fun i => (ht i).imp fun _ h => h.2)
  have hflat (s y : ℝ) (ω : Ω) :
      (∑ a : Fin m × Fin r, (f a.1 a.2).field s y ω) = elementarySum b s y ω := by
    rw [Fintype.sum_prod_type]
    exact grid_refinement_field_sum b τ hmono hzero ht f hfield s y ω
  obtain ⟨d, hd⟩ := disjoint_elementary_clip (fun a : Fin m × Fin r => f a.1 a.2) M hM
    (grid_refinement_disjoint τ hmono f hfs hft hfd)
  let eqv := Fintype.equivFin (Fin m × Fin r)
  refine ⟨Fintype.card (Fin m × Fin r), fun i => d (eqv.symm i), fun s y ω => ?_⟩
  change (∑ i, (d (eqv.symm i)).field s y ω) = _
  rw [eqv.symm.sum_comp (fun a => (d a).field s y ω), hd, hflat, hbox]
  split_ifs
  · rfl
  · simp [min_eq_right hM, max_eq_right (neg_nonpos.mpr hM)]

private theorem bounded_ae_tendsto_eLpNorm {p : ℝ} (hp : 0 < p)
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k)) (C : ℝ)
    (hbound : ∀ k ω, |f k ω| ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) (ENNReal.ofReal p) P ^ 2) atTop (𝓝 0) := by
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hinner := tendsto_lintegral_of_dominated_convergence
    (μ := P) (F := fun k ω => ‖f k ω‖ₑ ^ p) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal C ^ p)
    (fun k => (hf k).enorm.pow_const _)
    (fun k => ae_of_all _ fun ω => ENNReal.rpow_le_rpow
      (by simpa only [← ofReal_norm, Real.norm_eq_abs] using
        ENNReal.ofReal_le_ofReal (hbound k ω)) hp.le)
    (by simp [lintegral_const, ENNReal.rpow_ne_top_of_nonneg hp.le])
    (hlim.mono fun ω hω => by
      simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos hp] using
        (ENNReal.continuous_rpow_const (y := p)).tendsto _ |>.comp hω.enorm)
  simp only [lintegral_zero] at hinner
  have hr := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto (0 : ℝ≥0∞) |>.comp hinner
  have heq (k : ℕ) := eLpNorm_eq_lintegral_rpow_enorm_toReal
    hpne ENNReal.ofReal_ne_top (hf k).aestronglyMeasurable (μ := P)
  simp only [ENNReal.toReal_ofReal hp.le] at heq
  have hnlim : Tendsto (fun k => eLpNorm (f k) (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← heq, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using hr
  simpa only [Function.comp_def, ENNReal.rpow_two, zero_pow (by decide : 2 ≠ 0)] using
    (ENNReal.continuous_rpow_const (y := 2)).tendsto (0 : ℝ≥0∞) |>.comp hnlim

private theorem bounded_box_ae_tendsto_mixedNorm {p : ℝ} (hp : 0 < p)
    (U : ℕ → ℝ → ℝ → Ω → ℝ)
    (hU : ∀ k, Measurable (fun q : ℝ × ℝ × Ω => U k q.1 q.2.1 q.2.2))
    (C T R : ℝ) (hbound : ∀ k s y ω, |U k s y ω| ≤ C)
    (hsupport : ∀ k s y ω, (s, y) ∉ Ioc 0 T ×ˢ Icc (-R) R → U k s y ω = 0)
    (hlim : ∀ᵐ q ∂spaceTimeSample P,
      Tendsto (fun k => U k q.1 q.2.1 q.2.2) atTop (𝓝 0)) :
    Tendsto (fun k => mixedNormSq P p (U k)) atTop (𝓝 0) := by
  classical
  let K : Set (ℝ × ℝ) := Ioc 0 T ×ˢ Icc (-R) R
  have hK : MeasurableSet K := measurableSet_Ioc.prod measurableSet_Icc
  have hKfin : timeSpaceVolume K ≠ ∞ := by
    rw [timeSpaceVolume, Measure.prod_prod]
    apply ENNReal.mul_ne_top
    · exact ne_of_lt ((Measure.restrict_apply_le _ _).trans_lt (by simp))
    · simp
  have hsec (k : ℕ) (z : ℝ × ℝ) : Measurable (U k z.1 z.2) :=
    (hU k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hnorm (k : ℕ) (z : ℝ × ℝ) :
      eLpNorm (U k z.1 z.2) (ENNReal.ofReal p) P ≤ ENNReal.ofReal C := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      eLpNorm_le_of_ae_bound (μ := P) (p := ENNReal.ofReal p) (hsec k z).aestronglyMeasurable
        (ae_of_all _ fun ω => hbound k z.1 z.2 ω)
  have ha : ∀ᵐ q : (ℝ × ℝ) × Ω ∂timeSpaceVolume.prod P,
      Tendsto (fun k => U k q.1.1 q.1.2 q.2) atTop (𝓝 0) := by
    rw [spaceTimeSample_eq_map] at hlim
    exact ae_of_ae_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hlim
  have hsections := Measure.ae_ae_of_ae_prod ha
  have hout := tendsto_lintegral_of_dominated_convergence
    (μ := timeSpaceVolume)
    (F := fun k z => eLpNorm (U k z.1 z.2) (ENNReal.ofReal p) P ^ 2)
    (f := fun _ => 0) (K.indicator fun _ => ENNReal.ofReal C ^ 2)
    (fun k => (measurable_sample_eLpNorm hp (hU k)).pow_const 2)
    (fun k => ae_of_all _ fun z => ?_)
    (by rw [lintegral_indicator_const hK]; exact ENNReal.mul_ne_top (by finiteness) hKfin)
    (hsections.mono fun z hz => bounded_ae_tendsto_eLpNorm hp
      (fun k => U k z.1 z.2) (fun k => hsec k z) C
      (fun k ω => hbound k z.1 z.2 ω) hz)
  · simpa only [mixedNormSq, lintegral_zero] using hout
  · by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact pow_le_pow_left' (hnorm k z) 2
    · have he : U k z.1 z.2 = 0 := funext fun ω => hsupport k z.1 z.2 ω hz
      simp [he, indicator_of_notMem hz]

set_option linter.unusedVariables false in
/-- R1, bounded-box mixed-norm density. Elementary L² approximants can be
restricted to the same box and clipped to the same amplitude after refinement.
The number of elementary terms may vary with the approximation index.
Convergence concerns positive time only, as in `spaceTimeSample`. -/
theorem exists_elementary_approx_mixedNormSq {p : ℝ} (hp : 2 ≤ p)
    (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (M T R : ℝ) (hM : 0 < M) (hT : 0 < T) (hR : 0 < R)
    (hbound : ∀ s y ω, |G s y ω| ≤ M)
    (hsupport : ∀ s y ω, (s, y) ∉ Ioc 0 T ×ˢ Icc (-R) R → G s y ω = 0) :
    ∃ (N : ℕ → ℕ) (e : (k : ℕ) → Fin (N k) → Elementary F),
      (∀ k s y ω, |elementarySum (e k) s y ω| ≤ M) ∧
      (∀ k s y ω, (s, y) ∉ Ioc 0 T ×ˢ Icc (-R) R →
        elementarySum (e k) s y ω = 0) ∧
      Tendsto (fun k => mixedNormSq P p
        (fun s y ω => elementarySum (e k) s y ω - G s y ω)) atTop (𝓝 0) := by
  classical
  have hdomain := bounded_box_inDomain (P := P) G hG M T R hbound hsupport
  obtain ⟨N, e, hae⟩ := exists_elementarySum_tendsto_ae G hdomain
  choose L d hd using fun k => exists_elementary_clip_box (e k) M T R hM.le hT
  have hdbound (k : ℕ) (s y : ℝ) (ω : Ω) : |elementarySum (d k) s y ω| ≤ M := by
    rw [hd]
    split_ifs
    · rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    · simpa using hM.le
  have hdsupport (k : ℕ) (s y : ℝ) (ω : Ω)
      (hz : (s, y) ∉ Ioc 0 T ×ˢ Icc (-R) R) : elementarySum (d k) s y ω = 0 := by
    simp only [hd, ite_eq_right hz]
  refine ⟨L, d, hdbound, hdsupport, ?_⟩
  have hdm (k : ℕ) : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => elementarySum (d k) q.1 q.2.1 q.2.2) := by
    apply Finset.measurable_sum
    intro i _
    exact ((d k i).inDomain (P := P)).1
  apply bounded_box_ae_tendsto_mixedNorm (by linarith : 0 < p)
    (fun k s y ω => elementarySum (d k) s y ω - G s y ω)
    (fun k => ((hdm k).sub hG).mono (predictableSigma_le F) le_rfl) (2 * M) T R
  · intro k s y ω
    exact (abs_sub _ _).trans (by linarith [hdbound k s y ω, hbound s y ω])
  · intro k s y ω hz
    rw [hdsupport k s y ω hz, hsupport s y ω hz, sub_self]
  · filter_upwards [hae] with q hq
    by_cases hz : (q.1, q.2.1) ∈ Ioc 0 T ×ˢ Icc (-R) R
    · have hb := abs_le.mp (hbound q.1 q.2.1 q.2.2)
      have hl : Tendsto
          (fun k => max (-M) (min M (elementarySum (e k) q.1 q.2.1 q.2.2))) atTop
          (𝓝 (max (-M) (min M (G q.1 q.2.1 q.2.2)))) :=
        tendsto_const_nhds.max (tendsto_const_nhds.min hq)
      have hdl : Tendsto (fun k => elementarySum (d k) q.1 q.2.1 q.2.2) atTop
          (𝓝 (G q.1 q.2.1 q.2.2)) := by
        simpa only [hd, ite_eq_left hz, min_eq_right hb.2, max_eq_right hb.1] using hl
      simpa only [sub_self] using hdl.sub_const (G q.1 q.2.1 q.2.2)
    · simp only [hd, ite_eq_right hz, hsupport q.1 q.2.1 q.2.2 hz, sub_self]
      exact tendsto_const_nhds

/-- R1, removal of the bounded-box truncations. Each truncation is in the L²
domain, and the mixed-norm error tends to zero for every admissible input. -/
theorem truncateField_inDomain_and_tendsto {p : ℝ} (hp : 2 ≤ p)
    (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (hfin : mixedNormSq P p G < ⊤) :
    (∀ n, InDomain F P (truncateField n G)) ∧
      Tendsto (fun n => mixedNormSq P p
        (fun s y ω => truncateField n G s y ω - G s y ω)) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hm := hG.mono (predictableSigma_le F) le_rfl
  have htm (n : ℕ) := (truncateField_measurable n hG).mono (predictableSigma_le F) le_rfl
  have hsec (s y : ℝ) : Measurable (G s y) :=
    hm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have htsec (n : ℕ) (s y : ℝ) : Measurable (truncateField n G s y) :=
    (htm n).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hnorm := measurable_sample_eLpNorm (P := P) hp0 hm
  have herror (n : ℕ) := measurable_sample_eLpNorm (P := P)
    (G := fun s y ω => truncateField n G s y ω - G s y ω) hp0 ((htm n).sub hm)
  have herr_le (n : ℕ) (z : ℝ × ℝ) :
      eLpNorm (fun ω => truncateField n G z.1 z.2 ω - G z.1 z.2 ω) (ENNReal.ofReal p) P ≤
        eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P :=
    eLpNorm_mono ((htsec n z.1 z.2).sub (hsec z.1 z.2)).aestronglyMeasurable
      (fun ω => (truncateField_abs_le n G z.1 z.2 ω).2)
  constructor
  · intro n
    apply inDomain_of_mixedNormSq_lt_top hp (truncateField_measurable n hG)
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono
    intro z
    exact pow_le_pow_left' (eLpNorm_mono (htsec n z.1 z.2).aestronglyMeasurable
      (fun ω => (truncateField_abs_le n G z.1 z.2 ω).1)) 2
  · have hpos : ∀ᵐ z : ℝ × ℝ ∂timeSpaceVolume, 0 < z.1 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
      exact ae_of_all _ fun _ => hs
    have hfinite := ae_lt_top (hnorm.pow_const 2) hfin.ne
    have hlim : ∀ᵐ z : ℝ × ℝ ∂timeSpaceVolume,
        Tendsto (fun n => eLpNorm
          (fun ω => truncateField n G z.1 z.2 ω - G z.1 z.2 ω)
          (ENNReal.ofReal p) P ^ 2) atTop (𝓝 0) := by
      filter_upwards [hpos, hfinite] with z hz hzfin
      have hLp : MemLp (G z.1 z.2) (ENNReal.ofReal p) P :=
        (ENNReal.pow_lt_top_iff.mp hzfin).resolve_right (by norm_num)
      have hinner := tendsto_lintegral_of_dominated_convergence
        (μ := P) (F := fun n ω =>
          ‖truncateField n G z.1 z.2 ω - G z.1 z.2 ω‖ₑ ^ p)
        (f := fun _ => 0) (fun ω => ‖G z.1 z.2 ω‖ₑ ^ p)
        (fun n => ((htsec n z.1 z.2).sub (hsec z.1 z.2)).enorm.pow_const _)
        (fun n => ae_of_all _ fun ω => ENNReal.rpow_le_rpow
          (by simpa only [← ofReal_norm, Real.norm_eq_abs] using
            ENNReal.ofReal_le_ofReal (truncateField_abs_le n G z.1 z.2 ω).2) hp0.le)
        (by simpa only [ENNReal.toReal_ofReal hp0.le] using
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hpne ENNReal.ofReal_ne_top hLp).ne)
        (ae_of_all _ fun ω => ?_)
      · simp only [lintegral_zero] at hinner
        have hr := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto (0 : ℝ≥0∞) |>.comp hinner
        have heq (n : ℕ) := eLpNorm_eq_lintegral_rpow_enorm_toReal
          (f := fun ω => truncateField n G z.1 z.2 ω - G z.1 z.2 ω) hpne
          ENNReal.ofReal_ne_top ((htsec n z.1 z.2).sub (hsec z.1 z.2)).aestronglyMeasurable
          (μ := P)
        simp only [ENNReal.toReal_ofReal hp0.le] at heq
        have hnlim : Tendsto (fun n => eLpNorm
            (fun ω => truncateField n G z.1 z.2 ω - G z.1 z.2 ω)
            (ENNReal.ofReal p) P) atTop (𝓝 0) := by
          simpa only [Function.comp_def, ← heq, lintegral_zero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)]
            using hr
        simpa only [Function.comp_def, ENNReal.rpow_two, zero_pow (by decide : 2 ≠ 0)] using
          (ENNReal.continuous_rpow_const (y := 2)).tendsto (0 : ℝ≥0∞) |>.comp hnlim
      · apply tendsto_const_nhds.congr'
        filter_upwards [truncateField_eventually_eq G hz z.2 ω] with n hn
        simp [hn, ENNReal.zero_rpow_of_pos hp0]
    have hout := tendsto_lintegral_of_dominated_convergence
      (fun z : ℝ × ℝ => eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P ^ 2)
      (fun n => (herror n).pow_const 2)
      (fun n => ae_of_all _ fun z => pow_le_pow_left' (herr_le n z) 2)
      hfin.ne hlim
    simpa only [mixedNormSq, lintegral_zero] using hout

private theorem elementarySum_inDomain {n : ℕ} (e : Fin n → Elementary F) :
    InDomain F P (elementarySum e) := by
  have hm : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => elementarySum e q.1 q.2.1 q.2.2) := by
    exact Finset.measurable_sum _ (fun i _ => ((e i).inDomain (P := P)).1)
  have hl : MemLp (fun q : ℝ × ℝ × Ω => elementarySum e q.1 q.2.1 q.2.2) 2
      (spaceTimeSample P) := by
    exact memLp_finsetSum _ (fun i _ => (e i).inDomain.memLp)
  exact ⟨hm, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun _ => sq_nonneg _)).mp hl.integrable_sq.2⟩

private theorem walshT_elementarySum (hW : IsWhiteNoise P F W)
    {n : ℕ} (e : Fin n → Elementary F) :
    walshT hW (elementarySum e) =ᵐ[P] elementarySumIntegral W e := by
  classical
  have hd := elementarySum_inDomain (P := P) e
  have hc : toPredL2 (elementarySum e) hd = ∑ i, elementaryClass P (e i) := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [toPredL2_ae (elementarySum e) hd,
      Lp.coeFn_finsetSum Finset.univ (fun i => (elementaryClass P (e i)).val),
      ae_all_iff.mpr (fun i => toPredL2_ae (e i).field (e i).inDomain)] with q hq hs hi
    simp only [Submodule.coe_sum, hs, Finset.sum_apply]
    change (toPredL2 (elementarySum e) hd).val q =
      ∑ i, (toPredL2 (e i).field (e i).inDomain).val q
    simp only [hq, hi, elementarySum]
  have hw := walshT_ae_eq hW (elementarySum e) hd
  rw [hc, map_sum] at hw
  simp only [walshL2_elementary] at hw
  apply hw.trans
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => elementaryIntegral W (e i))] with ω hω
  simpa only [elementarySumIntegral, Finset.sum_apply] using hω

private theorem eLpNorm_two_sq_le_mixedNormSq {p : ℝ} (hp : 2 ≤ p)
    {G : ℝ → ℝ → Ω → ℝ}
    (hm : Measurable (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)) :
    eLpNorm (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) 2 (spaceTimeSample P) ^ 2 ≤
      mixedNormSq P p G := by
  have hsq : eLpNorm (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) 2
      (spaceTimeSample P) ^ 2 =
      ∫⁻ q, ENNReal.ofReal (G q.1 q.2.1 q.2.2 ^ 2) ∂spaceTimeSample P := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
      ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      using eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hm.aestronglyMeasurable
  rw [hsq, spaceTimeSample_eq_map,
    lintegral_map (hm.pow_const 2).ennreal_ofReal MeasurableEquiv.prodAssoc.measurable]
  have hm' : Measurable (fun q : (ℝ × ℝ) × Ω => G q.1.1 q.1.2 q.2) :=
    hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  change (∫⁻ q : (ℝ × ℝ) × Ω, ENNReal.ofReal (G q.1.1 q.1.2 q.2 ^ 2)
    ∂timeSpaceVolume.prod P) ≤ _
  rw [lintegral_prod _ (hm'.pow_const 2).ennreal_ofReal.aemeasurable]
  apply lintegral_mono
  intro z
  have hsec : Measurable (G z.1 z.2) :=
    hm'.comp (measurable_const.prodMk measurable_id)
  have hz : (∫⁻ ω, ENNReal.ofReal (G z.1 z.2 ω ^ 2) ∂P) =
      eLpNorm (G z.1 z.2) 2 P ^ 2 := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
      ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
        hsec.aestronglyMeasurable (μ := P)).symm
  change (∫⁻ ω, ENNReal.ofReal (G z.1 z.2 ω ^ 2) ∂P) ≤ _
  rw [hz]
  exact pow_le_pow_left' (eLpNorm_le_eLpNorm_of_exponent_le
    (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp))) 2

private theorem walshT_tendstoInMeasure_of_mixedNorm (hW : IsWhiteNoise P F W)
    {p : ℝ} (hp : 2 ≤ p) (U : ℕ → ℝ → ℝ → Ω → ℝ) (G : ℝ → ℝ → Ω → ℝ)
    (hU : ∀ k, InDomain F P (U k)) (hG : InDomain F P G)
    (hlim : Tendsto (fun k => mixedNormSq P p
      (fun s y ω => U k s y ω - G s y ω)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k => walshT hW (U k)) atTop (walshT hW G) := by
  have hsq : Tendsto (fun k => eLpNorm
      (fun q : ℝ × ℝ × Ω => U k q.1 q.2.1 q.2.2 - G q.1 q.2.1 q.2.2)
      2 (spaceTimeSample P) ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le)
    intro k
    exact eLpNorm_two_sq_le_mixedNormSq hp
      (G := fun s y ω => U k s y ω - G s y ω)
      (((hU k).1.sub hG.1).mono (predictableSigma_le F) le_rfl)
  have hl : Tendsto (fun k => eLpNorm
      (fun q : ℝ × ℝ × Ω => U k q.1 q.2.1 q.2.2 - G q.1 q.2.1 q.2.2)
      2 (spaceTimeSample P)) atTop (𝓝 0) := by
    simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one,
      ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)] using
      hsq.ennrpow_const ((2 : ℝ)⁻¹)
  have hc : Tendsto (fun k => toPredL2 (U k) (hU k)) atTop (𝓝 (toPredL2 G hG)) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun k => (hU k).memLp.toLp
      (fun q : ℝ × ℝ × Ω => U k q.1 q.2.1 q.2.2)) atTop
      (𝓝 (hG.memLp.toLp (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)))
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := 2) (μ := spaceTimeSample P)
      (fun k (q : ℝ × ℝ × Ω) => U k q.1 q.2.1 q.2.2) (fun k => (hU k).memLp)
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) hG.memLp).mpr hl
  have hw := (walshL2 hW).continuous.tendsto (toPredL2 G hG) |>.comp hc
  exact (tendstoInMeasure_of_tendsto_Lp hw).congr
    (fun k => (walshT_ae_eq hW (U k) (hU k)).symm) (walshT_ae_eq hW G hG).symm

private theorem mixedNormSq_sqrt_le {p : ℝ} (hp : 2 ≤ p)
    (U G : ℝ → ℝ → Ω → ℝ)
    (hU : Measurable (fun q : ℝ × ℝ × Ω => U q.1 q.2.1 q.2.2))
    (hG : Measurable (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2)) :
    mixedNormSq P p U ^ ((2 : ℝ)⁻¹) ≤
      mixedNormSq P p (fun s y ω => U s y ω - G s y ω) ^ ((2 : ℝ)⁻¹) +
        mixedNormSq P p G ^ ((2 : ℝ)⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have he := measurable_sample_eLpNorm (P := P)
    (G := fun s y ω => U s y ω - G s y ω) hp0 (hU.sub hG)
  have hg := measurable_sample_eLpNorm (P := P) hp0 hG
  have hpoint (z : ℝ × ℝ) : eLpNorm (U z.1 z.2) (ENNReal.ofReal p) P ≤
      eLpNorm (fun ω => U z.1 z.2 ω - G z.1 z.2 ω) (ENNReal.ofReal p) P +
        eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P := by
    have hid : U z.1 z.2 = (U z.1 z.2 - G z.1 z.2) + G z.1 z.2 := by
      ext ω
      simp
    calc
      _ = eLpNorm ((U z.1 z.2 - G z.1 z.2) + G z.1 z.2) (ENNReal.ofReal p) P :=
        congrArg (fun f => eLpNorm f (ENNReal.ofReal p) P) hid
      _ ≤ _ := eLpNorm_add_le hp1
  calc
    _ ≤ (∫⁻ z : ℝ × ℝ,
        (eLpNorm (fun ω => U z.1 z.2 ω - G z.1 z.2 ω) (ENNReal.ofReal p) P +
          eLpNorm (G z.1 z.2) (ENNReal.ofReal p) P) ^ 2
        ∂timeSpaceVolume) ^ ((2 : ℝ)⁻¹) := by
      exact ENNReal.rpow_le_rpow (lintegral_mono fun z =>
        pow_le_pow_left' (hpoint z) 2) (by norm_num)
    _ ≤ _ := by
      simpa only [mixedNormSq, one_div, ENNReal.rpow_two, Pi.add_apply] using
        ENNReal.lintegral_Lp_add_le he.aemeasurable hg.aemeasurable (by norm_num : (1 : ℝ) ≤ 2)

omit [IsProbabilityMeasure P] in
private theorem eLpNorm_le_of_tendstoInMeasure_bound
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (q : ℝ≥0∞)
    (hX : ∀ k, AEStronglyMeasurable (X k) P) (hY : AEStronglyMeasurable Y P)
    (hlim : TendstoInMeasure P X atTop Y) (B : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hB : Tendsto B atTop (𝓝 C)) (hbound : ∀ k, eLpNorm (X k) q P ≤ B k) :
    eLpNorm Y q P ≤ C := by
  obtain ⟨ns, hns, hae⟩ := hlim.exists_seq_tendsto_ae
  calc
    _ ≤ atTop.liminf (fun k => eLpNorm (X (ns k)) q P) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => hX (ns k)) Y hY hae
    _ ≤ atTop.liminf (fun k => B (ns k)) :=
      liminf_le_liminf (Eventually.of_forall fun k => hbound (ns k))
    _ = C := (hB.comp hns.tendsto_atTop).liminf_eq

private theorem moment_bound_of_mixedNorm_tendsto (hW : IsWhiteNoise P F W)
    {p : ℝ} (hp : 2 ≤ p) (U : ℕ → ℝ → ℝ → Ω → ℝ) (G : ℝ → ℝ → Ω → ℝ)
    (hU : ∀ k, InDomain F P (U k)) (hG : InDomain F P G)
    (hlim : Tendsto (fun k => mixedNormSq P p
      (fun s y ω => U k s y ω - G s y ω)) atTop (𝓝 0))
    (hbound : ∀ k, eLpNorm (walshT hW (U k)) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (bdgConst p) * mixedNormSq P p (U k)) :
    eLpNorm (walshT hW G) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (bdgConst p) * mixedNormSq P p G := by
  let c := ENNReal.ofReal (bdgConst p)
  let B : ℕ → ℝ≥0∞ := fun k => c ^ ((2 : ℝ)⁻¹) *
    (mixedNormSq P p (fun s y ω => U k s y ω - G s y ω) ^ ((2 : ℝ)⁻¹) +
      mixedNormSq P p G ^ ((2 : ℝ)⁻¹))
  have hB : Tendsto B atTop
      (𝓝 (c ^ ((2 : ℝ)⁻¹) * mixedNormSq P p G ^ ((2 : ℝ)⁻¹))) := by
    have hr := (hlim.ennrpow_const ((2 : ℝ)⁻¹)).add
      (tendsto_const_nhds (x := mixedNormSq P p G ^ ((2 : ℝ)⁻¹)))
    simpa only [B, ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹), zero_add]
      using ENNReal.Tendsto.const_mul (a := c ^ ((2 : ℝ)⁻¹)) hr
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  have hb (k : ℕ) : eLpNorm (walshT hW (U k)) (ENNReal.ofReal p) P ≤ B k := by
    have hs : eLpNorm (walshT hW (U k)) (ENNReal.ofReal p) P ≤
        (c * mixedNormSq P p (U k)) ^ ((2 : ℝ)⁻¹) := by
      apply (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).mpr
      simpa only [ENNReal.rpow_two] using hbound k
    apply hs.trans
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ)⁻¹)]
    exact mul_le_mul le_rfl (mixedNormSq_sqrt_le hp (U k) G
      ((hU k).1.mono (predictableSigma_le F) le_rfl)
      (hG.1.mono (predictableSigma_le F) le_rfl)) zero_le zero_le
  have hmeas (V : ℝ → ℝ → Ω → ℝ) (hV : InDomain F P V) :
      AEStronglyMeasurable (walshT hW V) P :=
    (Lp.aestronglyMeasurable (walshL2 hW (toPredL2 V hV))).congr (walshT_ae_eq hW V hV).symm
  have hf := eLpNorm_le_of_tendstoInMeasure_bound
    (fun k => walshT hW (U k)) (walshT hW G) (ENNReal.ofReal p)
    (fun k => hmeas (U k) (hU k)) (hmeas G hG)
    (walshT_tendstoInMeasure_of_mixedNorm hW hp U G hU hG hlim) B _ hB hb
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ)⁻¹)] at hf
  simpa only [ENNReal.rpow_two] using
    (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).mp hf

private theorem bounded_box_moment_bound (hW : IsWhiteNoise P F W)
    {p : ℝ} (hp : 2 ≤ p) (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (M T R : ℝ) (hM : 0 < M) (hT : 0 < T) (hR : 0 < R)
    (hbound : ∀ s y ω, |G s y ω| ≤ M)
    (hsupport : ∀ s y ω, (s, y) ∉ Ioc 0 T ×ˢ Icc (-R) R → G s y ω = 0) :
    eLpNorm (walshT hW G) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (bdgConst p) * mixedNormSq P p G := by
  obtain ⟨N, e, _, _, hlim⟩ :=
    exists_elementary_approx_mixedNormSq (P := P) hp G hG M T R hM hT hR hbound hsupport
  apply moment_bound_of_mixedNorm_tendsto hW hp (fun k => elementarySum (e k)) G
    (fun k => elementarySum_inDomain (e k))
    (bounded_box_inDomain G hG M T R hbound hsupport) hlim
  intro k
  rw [eLpNorm_congr_ae (walshT_elementarySum hW (e k))]
  exact eLpNorm_elementarySumIntegral_sq_le hW hp (e k)

/-- the corresponding interface full real-p bound for the constructed, totalized Walsh integral.
The hypotheses imply `InDomain F P G` by `inDomain_of_mixedNormSq_lt_top`;
in particular this is a bound for the genuine L² integral on the entire stated
domain, not a consequence of the off-domain zero convention. -/
theorem eLpNorm_walshT_sq_le (hW : IsWhiteNoise P F W) {p : ℝ} (hp : 2 ≤ p)
    (G : ℝ → ℝ → Ω → ℝ)
    (hG : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2))
    (hfin : mixedNormSq P p G < ⊤) :
    eLpNorm (walshT hW G) (ENNReal.ofReal p) P ^ 2 ≤
      ENNReal.ofReal (bdgConst p) * mixedNormSq P p G := by
  obtain ⟨ht, hlim⟩ := truncateField_inDomain_and_tendsto hp G hG hfin
  apply moment_bound_of_mixedNorm_tendsto hW hp (fun n => truncateField n G) G ht
    (inDomain_of_mixedNormSq_lt_top hp hG hfin) hlim
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply bounded_box_moment_bound hW hp (truncateField n G) (truncateField_measurable n hG)
    ((n : ℝ) + 1) ((n : ℝ) + 1) ((n : ℝ) + 1) hn1 hn1 hn1
  · intro s y ω
    unfold truncateField
    split_ifs
    · rw [abs_le]
      constructor
      · linarith [le_max_left (-(n : ℝ)) (min (n : ℝ) (G s y ω))]
      · exact max_le (by linarith) ((min_le_left _ _).trans (by linarith))
    · simpa using hn1.le
  · intro s y ω hz
    unfold truncateField
    split_ifs with h
    · exfalso
      apply hz
      simp only [mem_prod, mem_Ioc, mem_Icc]
      exact ⟨⟨h.1, by linarith [h.2.1]⟩,
        ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩⟩
    · rfl

end WalshIntegral.MomentBound
