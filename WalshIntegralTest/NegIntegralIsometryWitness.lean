module

public import WalshIntegral

@[expose] public section

noncomputable section

open MeasureTheory WalshIntegral.WhiteNoise WalshIntegral.Integral
open scoped ENNReal NNReal

namespace WalshIntegralTest.NegIntegralIsometry

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

theorem integral_norm {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) :
    ‖walshL2 hW (elementaryClass P (unitElementary F))‖ = 1 := by
  rw [norm_walshL2, unitElementary_norm]

end WalshIntegralTest.NegIntegralIsometry
