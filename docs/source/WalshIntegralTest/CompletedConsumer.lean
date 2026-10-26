module

public import WalshIntegral

@[expose] public section

/-!
# A concrete nonzero stochastic-integral consumer.
The concrete terminal theorem constructs completed-product white noise, checks the
nondegenerate unit rectangle law, and computes a nonzero Walsh integral via Itô isometry.
The unit elementary definition and its norm proof are copied from the existing compiled
NegIntegralIsometryWitness, changing only the enclosing namespace.
-/

noncomputable section

open MeasureTheory ProbabilityTheory WalshIntegral.WhiteNoise WalshIntegral.Integral
open scoped ENNReal NNReal

namespace WalshIntegralTest.CompletedConsumer

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}

def unitElementary (F : Filtration ℝ≥0 mΩ) : Elementary F where
  s := 0
  t := 1
  s_lt_t := by norm_num
  A := Set.Ioc 0 1
  measurableSet_A := measurableSet_Ioc
  volume_A_ne_top := by simp
  coeff := fun _ => 1
  measurable_coeff := measurable_const
  bounded_coeff := ⟨1, fun _ => by simp⟩

theorem unitElementary_norm : ‖elementaryClass P (unitElementary F)‖ = 1 := by
  let D : Set (ℝ × ℝ × Ω) := Set.Ioc 0 1 ×ˢ (Set.Ioc 0 1 ×ˢ Set.univ)
  have hD : MeasurableSet D :=
    measurableSet_Ioc.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hμ : spaceTimeSample P D = 1 := by
    norm_num [D, spaceTimeSample, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
      Set.Ioc_inter_Ioi]
  have hfin : spaceTimeSample P D ≠ ∞ := by rw [hμ]; simp
  have he : (elementaryClass P (unitElementary F)).val =
      indicatorConstLp 2 hD hfin (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [toPredL2_ae (unitElementary F).field
      ((unitElementary F).inDomain (P := P)),
      (indicatorConstLp_coeFn (p := 2) (hs := hD) (hμs := hfin) (c := (1 : ℝ)))]
      with q hq hq'
    change (toPredL2 (unitElementary F).field _).val q = _
    rw [hq, hq']
    simp [Elementary.field, unitElementary, D, Set.indicator_apply, Set.mem_prod]
  change ‖(elementaryClass P (unitElementary F)).val‖ = 1
  rw [he, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Measure.real, hμ]

/-- A fully instantiated, nonzero stochastic consumer on the completed Gaussian product. -/
theorem completed_noise_unit_rectangle_and_ito :
    ∃ (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace CompletedSample))
      (W : H →L[ℝ] Lp ℝ 2 completedProductGaussian)
      (hW : IsWhiteNoise completedProductGaussian F W),
      IsCompletedNatural completedProductGaussian F W ∧
      W ≠ 0 ∧
      completedProductGaussian.map (fun ω =>
        W (rectangle 0 1 (Set.Ioc 0 1) measurableSet_Ioc (by simp)) ω) =
          gaussianReal 0 1 ∧
      ‖walshL2 hW (elementaryClass completedProductGaussian (unitElementary F))‖ = 1 ∧
      (∫ ω, (walshL2 hW
        (elementaryClass completedProductGaussian (unitElementary F)) ω) ^ 2
          ∂completedProductGaussian) = 1 := by
  obtain ⟨F, W, e, ξ, hW, hF, hcoord, hseries⟩ := exists_completed_whiteNoise
  refine ⟨F, W, hW, hF, hW.ne_zero, ?_, ?_, ?_⟩
  · simpa using hW.rectangle_law 0 1 (by norm_num)
      (Set.Ioc 0 1) measurableSet_Ioc (by simp)
  · rw [norm_walshL2, unitElementary_norm]
  · rw [integral_sq_walshL2]
    have hi := real_inner_self_eq_norm_sq
      (elementaryClass completedProductGaussian (unitElementary F))
    rw [unitElementary_norm] at hi
    simpa only [Submodule.coe_inner, L2.inner_def, RCLike.inner_apply,
      conj_trivial, ← sq, one_pow] using hi

end WalshIntegralTest.CompletedConsumer
