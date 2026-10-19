import WalshIntegral

open MeasureTheory ProbabilityTheory WalshIntegral.WhiteNoise

namespace WalshIntegralTest.NegCovarianceSign

theorem covariance_correct {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (h g : H) :
    covariance (fun ω => W h ω) (fun ω => W g ω) P = inner ℝ h g := by
  exact hW.covariance_eq_inner h g

theorem not_negative_covariance {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration NNReal mΩ} {W : H →L[ℝ] Lp ℝ 2 P}
    (hW : IsWhiteNoise P F W) :
    ¬ ∀ h g : H,
      covariance (fun ω => W h ω) (fun ω => W g ω) P = -inner ℝ h g := by
  let := H_nontrivial
  obtain ⟨h, hh⟩ := exists_ne (0 : H)
  intro hfalse
  have hbad := hfalse h h
  rw [covariance_correct hW h h] at hbad
  have hpos : 0 < inner ℝ h h := real_inner_self_pos.mpr hh
  linarith

end WalshIntegralTest.NegCovarianceSign
