module

public import WalshIntegral
public import WalshIntegralTest.CompletedConsumer

open MeasureTheory WalshIntegral.WhiteNoise

/-- A white noise is never the zero map. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) : W ≠ 0 :=
  hW.ne_zero

/-- A white noise preserves the `L²` norm. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W) (h : H) :
    ‖W h‖ = ‖h‖ :=
  hW.norm_map h
