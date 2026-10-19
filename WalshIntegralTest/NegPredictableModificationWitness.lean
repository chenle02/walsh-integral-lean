import WalshIntegral.Modification

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace WalshIntegralTest.NegPredictableModification

open WalshIntegral.Predictable

scoped instance boolMeasurableSpace : MeasurableSpace Bool := ⊤

def P : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac true +
  (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance probabilityMeasure : IsProbabilityMeasure P := ⟨by
  simp only [P, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.add_div]
  norm_num only [one_add_one_eq_two]
  exact ENNReal.div_self (by norm_num) (by norm_num)⟩

def Z (ω : Bool) : ℝ := if ω then 1 else -1

theorem sign_measurable : Measurable Z := measurable_from_top

theorem sign_norm (ω : Bool) : ‖Z ω‖ = 1 := by cases ω <;> norm_num [Z]

theorem sign_memLp : MemLp Z 2 P := by
  apply MemLp.of_bound sign_measurable.aestronglyMeasurable 1
  exact ae_of_all _ fun ω => (sign_norm ω).le

theorem sign_mean : ∫ ω, Z ω ∂P = 0 := by
  rw [P, integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num))]
  norm_num [integral_smul_measure, Z]

theorem sign_eLpNorm : eLpNorm Z 2 P = 1 := by
  calc
    _ = eLpNorm (fun _ : Bool => (1 : ℝ)) 2 P :=
      eLpNorm_congr_norm_ae sign_measurable.aestronglyMeasurable
        aestronglyMeasurable_const (ae_of_all _ fun ω => by rw [sign_norm]; norm_num)
    _ = 1 := by
      rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne P), measure_univ]
      norm_num

theorem ae_all {p : Bool → Prop} : (∀ᵐ ω ∂P, p ω) ↔ ∀ ω, p ω := by
  simp only [P, ae_add_measure_iff,
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)]
  rw [ae_dirac_iff (MeasurableSpace.measurableSet_top),
    ae_dirac_iff (MeasurableSpace.measurableSet_top)]
  exact ⟨fun h ω => by cases ω; exact h.2; exact h.1, fun h => ⟨h true, h false⟩⟩

def F : Filtration ℝ≥0 (⊤ : MeasurableSpace Bool) := Filtration.const ℝ≥0 ⊥ bot_le

theorem section_measurable (t x : ℝ) :
    @Measurable Bool (ℝ × ℝ × Bool) ⊥ (predictableSigma F)
      (fun ω => (t, x, ω)) := by
  let : MeasurableSpace Bool := ⊥
  unfold predictableSigma
  apply measurable_generateFrom
  rintro S (⟨s, u, A, B, _, _, hB, rfl⟩ | ⟨C, A, B, _, _, _, hB, rfl⟩)
  · change MeasurableSet[⊥] B at hB
    exact (MeasurableSet.const (α := Bool) (t ∈ Ioc (s : ℝ) (u : ℝ))).inter
      ((MeasurableSet.const (α := Bool) (x ∈ A)).inter hB)
  · change MeasurableSet[⊥] B at hB
    exact (MeasurableSet.const (α := Bool) (t ∈ C)).inter
      ((MeasurableSet.const (α := Bool) (x ∈ A)).inter hB)

theorem bottom_constant {f : Bool → ℝ} (hf : Measurable[⊥] f) : f true = f false := by
  have h := MeasurableSpace.measurableSet_bot_iff.mp (hf (measurableSet_singleton (f true)))
  rcases h with h | h
  · have : true ∈ f ⁻¹' {f true} := by simp
    rw [h] at this
    exact this.elim
  · have : false ∈ f ⁻¹' {f true} := by rw [h]; trivial
    exact (mem_singleton_iff.mp this).symm


def X (t _x : ℝ) (ω : Bool) : ℝ := max t 0 * Z ω

theorem memLp_X (t x : ℝ) : MemLp (X t x) 2 P :=
  sign_memLp.const_mul (max t 0)

theorem zero_nonpos (t x : ℝ) (ht : t ≤ 0) : X t x =ᵐ[P] (fun _ => 0) := by
  apply ae_of_all
  intro ω
  simp [X, max_eq_right ht]

theorem increment_norm (t x u y : ℝ) :
    eLpNorm (fun ω => X t x ω - X u y ω) 2 P =
      ENNReal.ofReal |max t 0 - max u 0| := by
  have he : (fun ω => X t x ω - X u y ω) = (max t 0 - max u 0) • Z := by
    funext ω
    simp only [X, Pi.smul_apply, smul_eq_mul, sub_mul]
  rw [he, eLpNorm_const_smul, sign_eLpNorm, mul_one, ← ofReal_norm, Real.norm_eq_abs]

theorem l2_continuous (z : ℝ × ℝ) :
    Tendsto (fun z' : ℝ × ℝ => eLpNorm
      (fun ω => X z'.1 z'.2 ω - X z.1 z.2 ω) 2 P) (𝓝 z) (𝓝 0) := by
  simp_rw [increment_norm]
  have hc : Continuous (fun z' : ℝ × ℝ =>
      ENNReal.ofReal |max z'.1 0 - max z.1 0|) :=
    ENNReal.continuous_ofReal.comp
      (((continuous_fst.max continuous_const).sub continuous_const).abs)
  simpa using hc.tendsto z

theorem not_predictable :
    ¬ Measurable[predictableSigma F] (fun q : ℝ × ℝ × Bool => X q.1 q.2.1 q.2.2) := by
  intro h
  have hc := bottom_constant (h.comp (section_measurable 1 0))
  norm_num [X, Z] at hc

theorem no_modification : ¬ ∃ U : ℝ → ℝ → Bool → ℝ,
    Measurable[predictableSigma F] (fun q : ℝ × ℝ × Bool => U q.1 q.2.1 q.2.2) ∧
      ∀ t x, X t x =ᵐ[P] U t x := by
  rintro ⟨U, hU, he⟩
  have hc := bottom_constant (hU.comp (section_measurable 1 0))
  have ht := ae_all.mp (he 1 0) true
  have hf := ae_all.mp (he 1 0) false
  norm_num [X, Z] at ht hf
  exact (by norm_num : (1 : ℝ) ≠ -1) (ht.trans (hc.trans hf.symm))

end WalshIntegralTest.NegPredictableModification
