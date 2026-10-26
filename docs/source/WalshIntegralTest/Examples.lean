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

/-- The Walsh integral of a predictable L² integrand has mean zero. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} {W : H →L[ℝ] Lp ℝ 2 P} (hW : IsWhiteNoise P F W)
    (G : WalshIntegral.Integral.PredL2 F P) :
    ∫ ω, WalshIntegral.Integral.walshL2 hW G ω ∂P = 0 :=
  WalshIntegral.Integral.integral_walshL2 hW G

/-- A predictable field is `F t`-measurable at every time `t ≥ 0`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration NNReal mΩ}
    {f : ℝ × ℝ × Ω → ℝ}
    (hf : Measurable[WalshIntegral.Predictable.predictableSigma F] f) (t : NNReal) (x : ℝ) :
    Measurable[F t] (fun ω => f ((t : ℝ), x, ω)) :=
  WalshIntegral.Predictable.measurable_timeSection F hf t x
