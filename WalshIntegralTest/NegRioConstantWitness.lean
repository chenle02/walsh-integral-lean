module

public import WalshIntegral.Rio

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace WalshIntegralTest.NegRioConstant

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

def F : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · simp [hi]
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  le' _ := le_top

def d (k : ℕ) : Bool → ℝ := if k = 0 then Z else 0

theorem adapted (k : ℕ) : StronglyMeasurable[F (k + 1)] (d k) := by
  change StronglyMeasurable[if k + 1 = 0 then ⊥ else ⊤] (d k)
  exact measurable_from_top.stronglyMeasurable

theorem increments_memLp (k : ℕ) : MemLp (d k) (ENNReal.ofReal 2) P := by
  by_cases hk : k = 0
  · subst k
    simp [d]
  · simp [d, hk]

theorem centered (k : ℕ) : P[d k | F k] =ᵐ[P] (0 : Bool → ℝ) := by
  by_cases hk : k = 0
  · subst k
    change P[Z | ⊥] =ᵐ[P] _
    rw [condExp_bot, sign_mean]
    rfl
  · simp [d, hk]

theorem correct_rio :
    eLpNorm (fun ω => ∑ k ∈ Finset.range 1, d k ω) (ENNReal.ofReal 2) P ^ 2 ≤
      ENNReal.ofReal (2 - 1) *
        ∑ k ∈ Finset.range 1, eLpNorm (d k) (ENNReal.ofReal 2) P ^ 2 :=
  WalshIntegral.Rio.eLpNorm_sum_sq_le P F (by norm_num) d adapted increments_memLp centered 1

theorem smaller_constant_iff_false : (eLpNorm (fun ω => ∑ k ∈ Finset.range 1, d k ω) (ENNReal.ofReal 2) P ^ 2 ≤
      ENNReal.ofReal (2 - 2) *
        ∑ k ∈ Finset.range 1, eLpNorm (d k) (ENNReal.ofReal 2) P ^ 2) ↔ False := by
  norm_num [d, sign_eLpNorm]

end WalshIntegralTest.NegRioConstant
