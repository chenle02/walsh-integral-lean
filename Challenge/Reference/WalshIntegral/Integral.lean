module

public import Challenge.Reference.WalshIntegral.WhiteNoise
public import Challenge.Reference.WalshIntegral.Predictable

@[expose] public section
/-!
# The Walsh integral on predictable L² classes, its elementary agreement, Itô isometry, uniqueness and totalized representative API.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace WalshIntegral.Integral

open WalshIntegral.WhiteNoise WalshIntegral.Predictable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Positive-time, space, and sample measure in the predictable association. -/
def spaceTimeSample (P : Measure Ω) : Measure (ℝ × ℝ × Ω) :=
  (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.prod P)

/-- Reassociation identifies our measure with the white-noise time-space product. -/
theorem spaceTimeSample_eq_map (P : Measure Ω) [IsProbabilityMeasure P] :
    spaceTimeSample P =
      (timeSpaceVolume.prod P).map
        (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × Ω ≃ᵐ ℝ × ℝ × Ω) := by
  exact Measure.prodAssoc_prod.symm

/-- The submodule of L² classes admitting a predictable measurable representative. -/
abbrev predL2Submodule (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 (spaceTimeSample P)) :=
  lpMeas ℝ ℝ (predictableSigma F) 2 (spaceTimeSample P)

/-- Predictable L² integrands, with the norm and vector operations of the submodule. -/
abbrev PredL2 (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :=
  ↥(predL2Submodule F P)

/-- The predictable L² submodule is closed in the ambient L² space. -/
theorem isClosed_predL2 (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsClosed (predL2Submodule F P : Set (Lp ℝ 2 (spaceTimeSample P))) := by
  exact isClosed_aestronglyMeasurable (predictableSigma_le F)

/-- Completeness follows from the sub-sigma-algebra inclusion. -/
instance instCompleteSpacePredL2 (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    CompleteSpace (PredL2 F P) := by
  let : Fact (predictableSigma F ≤ Prod.instMeasurableSpace) :=
    ⟨predictableSigma_le F⟩
  unfold PredL2 predL2Submodule
  infer_instance

/-- The exact predictable, finite-variance domain used to totalize the integral. -/
def InDomain (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (G : ℝ → ℝ → Ω → ℝ) : Prop :=
  Measurable[predictableSigma F] (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) ∧
    (∫⁻ q : ℝ × ℝ × Ω, ENNReal.ofReal (G q.1 q.2.1 q.2.2 ^ 2)
      ∂spaceTimeSample P) < ∞

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- Finite variance and predictability imply ambient L² membership. -/
theorem InDomain.memLp {G : ℝ → ℝ → Ω → ℝ} (hG : InDomain F P G) :
    MemLp (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) 2 (spaceTimeSample P) := by
  have hm := (hG.1.mono (predictableSigma_le F) le_rfl).aestronglyMeasurable
    (μ := spaceTimeSample P)
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact ⟨hm.pow 2, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mpr hG.2⟩

/-- The L² class of a domain input admits that input as a predictable representative. -/
theorem InDomain.mem_predL2 {G : ℝ → ℝ → Ω → ℝ} (hG : InDomain F P G) :
    hG.memLp.toLp (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) ∈
      predL2Submodule F P := by
  exact mem_lpMeas_iff_aestronglyMeasurable.mpr
    (hG.1.stronglyMeasurable.aestronglyMeasurable.congr hG.memLp.coeFn_toLp.symm)

/-- Turn an actual domain integrand into its predictable L² class. -/
def toPredL2 (G : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) : PredL2 F P :=
  ⟨hG.memLp.toLp (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2), hG.mem_predL2⟩

/-- The class construction represents the supplied integrand almost everywhere. -/
theorem toPredL2_ae (G : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) :
    (fun q => (toPredL2 G hG).val q) =ᵐ[spaceTimeSample P]
      (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) := by
  exact hG.memLp.coeFn_toLp

/-- The finite-variance predictable domain is closed under addition. -/
theorem InDomain.add {G G' : ℝ → ℝ → Ω → ℝ}
    (hG : InDomain F P G) (hG' : InDomain F P G') :
    InDomain F P (fun s y ω => G s y ω + G' s y ω) := by
  refine ⟨hG.1.add hG'.1, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp
      (hG.memLp.add hG'.memLp).integrable_sq.2

/-- The finite-variance predictable domain is closed under real scalar multiplication. -/
theorem InDomain.smul {G : ℝ → ℝ → Ω → ℝ} (hG : InDomain F P G) (c : ℝ) :
    InDomain F P (fun s y ω => c * G s y ω) := by
  refine ⟨measurable_const.mul hG.1, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp
      (hG.memLp.const_mul c).integrable_sq.2

/-- A single random elementary integrand: a bounded past-measurable coefficient
and a finite spatial cell on a nonempty nonnegative-time interval. -/
structure Elementary (F : Filtration ℝ≥0 mΩ) where
  s : ℝ≥0
  t : ℝ≥0
  s_lt_t : s < t
  A : Set ℝ
  measurableSet_A : MeasurableSet A
  volume_A_ne_top : volume A ≠ ∞
  coeff : Ω → ℝ
  measurable_coeff : Measurable[F s] coeff
  bounded_coeff : ∃ C : ℝ, ∀ ω, ‖coeff ω‖ ≤ C

/-- The literal field `H * 1_{(s,t] × A}` associated with elementary data. -/
def Elementary.field (e : Elementary F) : ℝ → ℝ → Ω → ℝ :=
  fun r y ω => e.coeff ω *
    (Set.Ioc (e.s : ℝ) (e.t : ℝ) ×ˢ e.A).indicator (fun _ => 1) (r, y)

variable [IsProbabilityMeasure P]

/-- Every bounded random elementary field is in the predictable L² domain. -/
theorem Elementary.inDomain (e : Elementary F) : InDomain F P e.field := by
  classical
  let D : Set (ℝ × ℝ × Ω) :=
    Set.Ioc (e.s : ℝ) (e.t : ℝ) ×ˢ (e.A ×ˢ Set.univ)
  have hgen (B : Set Ω) (hB : MeasurableSet[F e.s] B) :
      MeasurableSet[predictableSigma F]
        (Set.Ioc (e.s : ℝ) (e.t : ℝ) ×ˢ (e.A ×ˢ B)) :=
    MeasurableSpace.measurableSet_generateFrom
      (Or.inl ⟨e.s, e.t, e.A, B, e.s_lt_t, e.measurableSet_A, hB, rfl⟩)
  have hD : MeasurableSet[predictableSigma F] D := hgen _ MeasurableSet.univ
  have hfield (q : ℝ × ℝ × Ω) :
      e.field q.1 q.2.1 q.2.2 = D.indicator (fun q => e.coeff q.2.2) q := by
    by_cases hq : q ∈ D
    · have hr : (q.1, q.2.1) ∈ Set.Ioc (e.s : ℝ) (e.t : ℝ) ×ˢ e.A :=
        ⟨hq.1, hq.2.1⟩
      simp [Elementary.field, Set.indicator_of_mem hq, Set.indicator_of_mem hr]
    · have hr : (q.1, q.2.1) ∉ Set.Ioc (e.s : ℝ) (e.t : ℝ) ×ˢ e.A := by
        simpa [D] using hq
      simp [Elementary.field, Set.indicator_of_notMem hq, Set.indicator_of_notMem hr]
  have hm : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => e.field q.1 q.2.1 q.2.2) := by
    intro S hS
    have hpre := hgen (e.coeff ⁻¹' S) (e.measurable_coeff hS)
    by_cases hzero : (0 : ℝ) ∈ S
    · convert hpre.union hD.compl using 1
      ext q
      simp only [(Set.mem_preimage), hfield, (Set.mem_union), (Set.mem_compl_iff)]
      by_cases hq : q ∈ D
      · simp [hq, hq.1, hq.2.1]
      · simp only [Set.indicator_of_notMem hq, hzero, not_false_eq_true,
          hq, or_true]
    · convert hpre using 1
      ext q
      simp only [(Set.mem_preimage), hfield]
      by_cases hq : q ∈ D
      · simp [Set.indicator_of_mem hq, hq.1, hq.2.1]
      · simp only [Set.indicator_of_notMem hq, hzero, false_iff]
        intro hr
        exact hq ⟨hr.1, hr.2.1, Set.mem_univ _⟩
  have hDfin : spaceTimeSample P D ≠ ∞ := by
    rw [spaceTimeSample, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one]
    apply ENNReal.mul_ne_top
    · exact ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _)
        (by simp : volume (Set.Ioc (e.s : ℝ) (e.t : ℝ)) < ∞))
    · exact e.volume_A_ne_top
  obtain ⟨C, hC⟩ := e.bounded_coeff
  have hLp : MemLp (fun q : ℝ × ℝ × Ω => e.field q.1 q.2.1 q.2.2) 2
      (spaceTimeSample P) := by
    apply (memLp_indicator_const 2 (predictableSigma_le F _ hD).nullMeasurableSet C
      (Or.inr hDfin)).of_le (hm.mono (predictableSigma_le F) le_rfl).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    rw [hfield]
    by_cases hq : q ∈ D
    · simpa only [Set.indicator_of_mem hq, Real.norm_eq_abs] using
        (hC q.2.2).trans (le_abs_self C)
    · simp only [Set.indicator_of_notMem hq, norm_zero, (le_refl)]
  exact ⟨hm, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hLp.integrable_sq.2⟩

/-- The predictable L² class of one elementary field. -/
def elementaryClass (P : Measure Ω) [IsProbabilityMeasure P]
    (e : Elementary F) : PredL2 F P :=
  toPredL2 e.field e.inDomain

set_option linter.unusedSectionVars false in
/-- Bounded multiplication of a noise rectangle gives a square-integrable variable.
This fact needs no white-noise law, only the L²-valued map. -/
theorem elementaryIntegral_memLp (W : H →L[ℝ] Lp ℝ 2 P) (e : Elementary F) :
    MemLp (fun ω => e.coeff ω *
      W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω) 2 P := by
  obtain ⟨C, hC⟩ := e.bounded_coeff
  have hm := (e.measurable_coeff.mono (F.le e.s) le_rfl).aestronglyMeasurable
    (μ := P)
  exact (memLp_top_of_bound hm C (Filter.Eventually.of_forall hC)).mul
    (Lp.memLp (W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top)))

/-- The elementary stochastic integral as the L² class of the literal product. -/
def elementaryIntegral (W : H →L[ℝ] Lp ℝ 2 P) (e : Elementary F) : Lp ℝ 2 P :=
  (elementaryIntegral_memLp W e).toLp (fun ω => e.coeff ω *
    W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω)

/-- The elementary integral represents the bounded coefficient times the increment. -/
theorem elementaryIntegral_ae (W : H →L[ℝ] Lp ℝ 2 P) (e : Elementary F) :
    (fun ω => elementaryIntegral W e ω) =ᵐ[P] (fun ω => e.coeff ω *
      W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω) := by
  exact (elementaryIntegral_memLp W e).coeFn_toLp

/-- Localize to finite sets and use uniqueness of vector measures on a pi-system. -/
theorem ae_zero_of_local_generator_integrals {α : Type*} [m : MeasurableSpace α]
    (μ : Measure α) (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (D : ℕ → Set α) (hD : ∀ n, MeasurableSet (D n))
    (hDfin : ∀ n, μ (D n) ≠ ∞) (hcover : ∀ᵐ x ∂μ, ∃ n, x ∈ D n)
    (f : Lp ℝ 2 μ)
    (hzero : ∀ n S, S ∈ C → ∫ x in S ∩ D n, f x ∂μ = 0)
    (hwhole : ∀ n, ∫ x in D n, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hn (n : ℕ) : (D n).indicator (fun x => f x) =ᵐ[μ] 0 := by
    have hi : Integrable ((D n).indicator (fun x => f x)) μ :=
      (integrable_indicator_iff (hD n)).mpr
        (integrableOn_Lp_of_measure_ne_top f (by norm_num) (hDfin n))
    apply hi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
    rw [withDensityᵥ_zero]
    refine VectorMeasure.ext_of_generateFrom C ?_ hgen hpi ?_
    · intro S hS
      have hm : MeasurableSet S := hgen ▸ MeasurableSpace.measurableSet_generateFrom hS
      rw [withDensityᵥ_apply hi hm, zero_apply,
        integral_indicator (hD n), Measure.restrict_restrict (hD n), Set.inter_comm]
      exact hzero n S hS
    · rw [withDensityᵥ_apply hi MeasurableSet.univ, zero_apply,
        Measure.restrict_univ, integral_indicator (hD n)]
      exact hwhole n
  filter_upwards [ae_all_iff.mpr hn, hcover] with x hx hcov
  obtain ⟨n, hn⟩ := hcov
  simpa only [Set.indicator_of_mem hn, Pi.zero_apply] using hx n



/-- The generating rectangles of `predictableSigma`, exposed for pi-system induction. -/
def predictableGenerators (F : Filtration ℝ≥0 mΩ) : Set (Set (ℝ × ℝ × Ω)) := {S |
  (∃ (s t : ℝ≥0) (A : Set ℝ) (B : Set Ω),
    s < t ∧ MeasurableSet A ∧ MeasurableSet[F s] B ∧
      S = Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B)) ∨
  (∃ (C A : Set ℝ) (B : Set Ω),
    MeasurableSet C ∧ C ⊆ Set.Iic 0 ∧ MeasurableSet A ∧ MeasurableSet[F 0] B ∧
      S = C ×ˢ (A ×ˢ B))}

theorem predictableGenerators_pi (F : Filtration ℝ≥0 mΩ) :
    IsPiSystem (predictableGenerators F) := by
  rintro S (⟨s, t, A, B, hst, hA, hB, rfl⟩ | ⟨C, A, B, hC, hC0, hA, hB, rfl⟩)
    T (⟨u, v, E, D, huv, hE, hD, rfl⟩ | ⟨C', E, D, hC', hC'0, hE, hD, rfl⟩) hne
  · obtain ⟨q, hq, hq'⟩ := hne
    refine Or.inl ⟨max s u, min t v, A ∩ E, B ∩ D, ?_, hA.inter hE,
      (F.mono (le_max_left _ _) _ hB).inter (F.mono (le_max_right _ _) _ hD), ?_⟩
    · apply NNReal.coe_lt_coe.mp
      simp only [NNReal.coe_max, NNReal.coe_min, (max_lt_iff), (lt_min_iff)]
      constructor <;> constructor <;>
        linarith [hq.1.1, hq.1.2, hq'.1.1, hq'.1.2]
    · ext q
      simp only [(Set.mem_inter_iff), (Set.mem_prod), (Set.mem_Ioc),
        NNReal.coe_max, NNReal.coe_min, (max_lt_iff), (le_min_iff)]
      tauto
  · obtain ⟨q, hq, hq'⟩ := hne
    exact False.elim ((not_lt_of_ge (hC'0 hq'.1)) (lt_of_le_of_lt s.coe_nonneg hq.1.1))
  · obtain ⟨q, hq, hq'⟩ := hne
    exact False.elim ((not_lt_of_ge (hC0 hq.1)) (lt_of_le_of_lt u.coe_nonneg hq'.1.1))
  · refine Or.inr ⟨C ∩ C', A ∩ E, B ∩ D, hC.inter hC',
      fun q hq => hC0 hq.1, hA.inter hE, hB.inter hD, ?_⟩
    ext q
    simp only [(Set.mem_inter_iff), (Set.mem_prod)]
    tauto


/-- Finite real linear combinations of the random elementary classes are dense. -/
theorem dense_elementary :
    Dense (Submodule.span ℝ (Set.range (elementaryClass (F := F) P)) :
      Set (PredL2 F P)) := by
  classical
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  let E := lpMeasToLpTrimLie ℝ ℝ 2 (spaceTimeSample P) (predictableSigma_le F)
  let g := E f
  have hga : (fun q => g q) =ᵐ[spaceTimeSample P] (fun q => f.val q) :=
    lpMeasToLpTrim_ae_eq (predictableSigma_le F) f
  have hbox (s t : ℝ≥0) (hst : s < t) (A : Set ℝ) (hA : MeasurableSet A)
      (hAfin : volume A ≠ ∞) (B : Set Ω) (hB : MeasurableSet[F s] B) :
      ∫ q in Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B), g q
        ∂(spaceTimeSample P).trim (predictableSigma_le F) = 0 := by
    let e : Elementary F := ⟨s, t, hst, A, hA, hAfin, B.indicator (fun _ => 1),
      measurable_const.indicator hB, ⟨1, fun ω => by
        by_cases hω : ω ∈ B <;> simp [hω]⟩⟩
    have hs : MeasurableSet[predictableSigma F]
        (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B)) :=
      MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨s, t, A, B, hst, hA, hB, rfl⟩)
    rw [← setIntegral_trim (predictableSigma_le F) (Lp.stronglyMeasurable g) hs]
    have he : inner ℝ (elementaryClass P e) f =
        ∫ q in Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B), f.val q ∂spaceTimeSample P := by
      rw [Submodule.coe_inner, L2.inner_def]
      rw [← integral_indicator (predictableSigma_le F _ hs)]
      apply integral_congr_ae
      filter_upwards [toPredL2_ae e.field (e.inDomain (P := P))] with q hq
      change (inner ℝ ((toPredL2 e.field (e.inDomain (P := P))).val q) (f.val q)) = _
      rw [hq]
      simp only [Elementary.field, e, RCLike.inner_apply, conj_trivial]
      by_cases ht : q.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) <;>
        by_cases hy : q.2.1 ∈ A <;> by_cases hω : q.2.2 ∈ B <;>
        simp [(Set.mem_prod), ht, hy, hω]
    rw [integral_congr_ae (ae_restrict_of_ae hga), ← he]
    have hem : elementaryClass P e ∈
        Submodule.span ℝ (Set.range (elementaryClass (F := F) P)) :=
      Submodule.subset_span ⟨e, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hem hf
  let D : ℕ → Set (ℝ × ℝ × Ω) := fun n =>
    Set.Ioc 0 (n + 1 : ℝ) ×ˢ (Set.Icc (-(n : ℝ)) n ×ˢ Set.univ)
  have hDc (n : ℕ) : D n ∈ predictableGenerators F := by
    exact Or.inl ⟨0, n + 1, Set.Icc (-(n : ℝ)) n, Set.univ, by positivity,
      measurableSet_Icc, MeasurableSet.univ, by simp [D]⟩
  have hDm (n : ℕ) : MeasurableSet[predictableSigma F] (D n) :=
    MeasurableSpace.measurableSet_generateFrom (hDc n)
  have hDf (n : ℕ) : (spaceTimeSample P).trim (predictableSigma_le F) (D n) ≠ ∞ := by
    rw [trim_measurableSet_eq _ (hDm n)]
    simp only [D, spaceTimeSample, Measure.prod_prod, measure_univ, mul_one]
    apply ENNReal.mul_ne_top
    · exact ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _)
        (by simp : volume (Set.Ioc (0 : ℝ) (n + 1)) < ∞))
    · simp
  have hcover : ∀ᵐ q ∂(spaceTimeSample P).trim (predictableSigma_le F), ∃ n, q ∈ D n := by
    change (spaceTimeSample P).trim (predictableSigma_le F) {q | ∃ n, q ∈ D n}ᶜ = 0
    have hm : MeasurableSet[predictableSigma F] {q | ∃ n, q ∈ D n} := by
      convert MeasurableSet.iUnion hDm using 1
      ext q
      simp only [Set.mem_ofPred_eq, (Set.mem_iUnion)]
    rw [trim_measurableSet_eq _ hm.compl]
    have hpos : ∀ᵐ q ∂spaceTimeSample P, 0 < q.1 := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_lt measurable_const measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact Filter.Eventually.of_forall fun _ => hs
    filter_upwards [hpos] with q hq
    obtain ⟨n, hn⟩ := exists_nat_gt (max q.1 |q.2.1|)
    have ht := lt_of_le_of_lt (le_max_left _ _) hn
    have hx := lt_of_le_of_lt (le_max_right _ _) hn
    refine ⟨n, ⟨hq, by linarith⟩, ⟨?_, ?_⟩, Set.mem_univ _⟩
    · linarith [neg_abs_le q.2.1]
    · linarith [le_abs_self q.2.1]
  have hgz : g =ᵐ[(spaceTimeSample P).trim (predictableSigma_le F)] 0 := by
    refine @ae_zero_of_local_generator_integrals (ℝ × ℝ × Ω) (predictableSigma F)
      ((spaceTimeSample P).trim (predictableSigma_le F)) (predictableGenerators F) rfl
      (predictableGenerators_pi F) D hDm hDf hcover g ?_ ?_
    · intro n S hS
      rcases hS with ⟨s, t, A, B, hst, hA, hB, rfl⟩ |
        ⟨C, A, B, hC, hC0, hA, hB, rfl⟩
      · by_cases ht : s < min t (n + 1 : ℝ≥0)
        · have heq : (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B)) ∩ D n =
              Set.Ioc (s : ℝ) (min t (n + 1 : ℝ≥0) : ℝ≥0) ×ˢ
                ((A ∩ Set.Icc (-(n : ℝ)) n) ×ˢ B) := by
            ext q
            simp only [D, (Set.mem_inter_iff), (Set.mem_prod), (Set.mem_Ioc), (Set.mem_Icc),
              (Set.mem_univ), and_true, NNReal.coe_min, NNReal.coe_add,
              NNReal.coe_natCast, NNReal.coe_one, (le_min_iff)]
            constructor
            · tauto
            · rintro ⟨⟨hs, htt, htn⟩, ⟨hA, hx⟩, hB⟩
              exact ⟨⟨⟨hs, htt⟩, hA, hB⟩, ⟨lt_of_le_of_lt s.coe_nonneg hs, htn⟩, hx⟩
          rw [heq]
          exact hbox s _ ht _ (hA.inter measurableSet_Icc)
            (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp))) B hB
        · have heq : (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (A ×ˢ B)) ∩ D n = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro q ⟨hq, hq'⟩
            apply ht
            apply NNReal.coe_lt_coe.mp
            simp only [NNReal.coe_min, NNReal.coe_add, NNReal.coe_natCast,
              NNReal.coe_one, (lt_min_iff)]
            exact ⟨lt_of_lt_of_le hq.1.1 hq.1.2, lt_of_lt_of_le hq.1.1 hq'.1.2⟩
          simp only [heq, setIntegral_empty]
      · have heq : (C ×ˢ (A ×ˢ B)) ∩ D n = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro q ⟨hq, hq'⟩
          exact not_lt_of_ge (hC0 hq.1) hq'.1.1
        simp only [heq, setIntegral_empty]
    · intro n
      exact hbox 0 (n + 1) (by positivity) _ measurableSet_Icc (by simp)
        Set.univ MeasurableSet.univ
  have hfz : (fun q => f.val q) =ᵐ[spaceTimeSample P] 0 :=
    hga.symm.trans (ae_eq_of_ae_eq_trim hgz)
  apply Subtype.ext
  exact Lp.ext (hfz.trans (Lp.coeFn_zero _ _ _).symm)

variable {W : H →L[ℝ] Lp ℝ 2 P}

open ProbabilityTheory
open scoped BigOperators

theorem noise_mean_zero (hW : IsWhiteNoise P F W) (h : H) :
    ∫ ω, W h ω ∂P = 0 := by
  have heq := integral_id_gaussianReal (μ := 0) (v := ‖h‖₊ ^ 2)
  rw [← hW.gaussian h] at heq
  rw [integral_map (Lp.stronglyMeasurable (W h)).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x)
      (P.map (fun ω => W h ω)))] at heq
  exact heq

theorem noise_inner (hW : IsWhiteNoise P F W) (h g : H) :
    ∫ ω, W h ω * W g ω ∂P = inner ℝ h g := by
  let I : H →ₗᵢ[ℝ] Lp ℝ 2 P := { W.toLinearMap with norm_map' := hW.norm_map }
  have hi : inner ℝ (W h) (W g) = inner ℝ h g := I.inner_map_map h g
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using hi

set_option linter.unusedSectionVars false in
theorem future_measurable (s : ℝ≥0) (h : H) (hh : SupportedAfter s h) :
    Measurable[futureSigma W s] (fun ω => W h ω) := by
  apply Measurable.of_comap_le
  exact le_iSup (fun k : {h : H // SupportedAfter s h} =>
    MeasurableSpace.comap (fun ω => W k.val ω) inferInstance) ⟨h, hh⟩

theorem future_past_indep (hW : IsWhiteNoise P F W) (s : ℝ≥0)
    {X Y : Ω → ℝ} (hX : Measurable[F s] X)
    (hY : Measurable[futureSigma W s] Y) : IndepFun X Y P := by
  exact (indep_of_indep_of_le (hW.futureSigma_indep s) hY.comap_le hX.comap_le).symm

/-- Fubini separates the random coefficient from the deterministic rectangle pair. -/
theorem elementary_inner_factor (e d : Elementary F) :
    inner ℝ (elementaryClass P e) (elementaryClass P d) =
      (∫ ω, e.coeff ω * d.coeff ω ∂P) *
        inner ℝ (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top)
          (rectangle d.s d.t d.A d.measurableSet_A d.volume_A_ne_top) := by
  let : SFinite timeSpaceVolume := by
    unfold timeSpaceVolume
    infer_instance
  let a := (Set.Ioc (e.s : ℝ) (e.t : ℝ) ×ˢ e.A).indicator (fun _ => (1 : ℝ))
  let b := (Set.Ioc (d.s : ℝ) (d.t : ℝ) ×ˢ d.A).indicator (fun _ => (1 : ℝ))
  have he := e.inDomain (P := P)
  have hd := d.inDomain (P := P)
  have hm := (he.1.mono (predictableSigma_le F) le_rfl).mul
    (hd.1.mono (predictableSigma_le F) le_rfl)
  rw [Submodule.coe_inner, L2.inner_def]
  calc
    _ = ∫ q, e.field q.1 q.2.1 q.2.2 * d.field q.1 q.2.1 q.2.2 ∂spaceTimeSample P := by
      apply integral_congr_ae
      filter_upwards [toPredL2_ae e.field he, toPredL2_ae d.field hd] with q hq hq'
      change inner ℝ ((toPredL2 e.field he).val q) ((toPredL2 d.field hd).val q) = _
      simp only [hq, hq', RCLike.inner_apply, conj_trivial, mul_comm]
    _ = ∫ q : (ℝ × ℝ) × Ω, (a q.1 * b q.1) * (e.coeff q.2 * d.coeff q.2)
        ∂timeSpaceVolume.prod P := by
      rw [spaceTimeSample_eq_map]
      erw [integral_map (μ := timeSpaceVolume.prod P)
        MeasurableEquiv.prodAssoc.measurable.aemeasurable hm.aestronglyMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        change (e.coeff q.2 * a q.1) * (d.coeff q.2 * b q.1) = _
        ring
    _ = _ := by
      rw [integral_prod_mul (fun z => a z * b z) (fun ω => e.coeff ω * d.coeff ω), mul_comm]
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [rectangle_ae e.s e.t e.A e.measurableSet_A e.volume_A_ne_top,
        rectangle_ae d.s d.t d.A d.measurableSet_A d.volume_A_ne_top] with q hq hq'
      simp only [RCLike.inner_apply, conj_trivial, hq, hq', mul_comm, a, b]


theorem rectangle_split (s t u : ℝ≥0) (hsu : s ≤ u)
    (A : Set ℝ) (hA : MeasurableSet A) (hAfin : volume A ≠ ∞) :
    rectangle s t A hA hAfin =
      rectangle s (min t u) A hA hAfin + rectangle u t A hA hAfin := by
  apply Lp.ext
  filter_upwards [rectangle_ae s t A hA hAfin, rectangle_ae s (min t u) A hA hAfin,
    rectangle_ae u t A hA hAfin,
    Lp.coeFn_add (rectangle s (min t u) A hA hAfin) (rectangle u t A hA hAfin)]
    with q hq hp hf ha
  rw [ha, Pi.add_apply, hq, hp, hf]
  have hsu' := NNReal.coe_le_coe.mpr hsu
  by_cases hy : q.2 ∈ A
  · by_cases hs : (s : ℝ) < q.1 <;> by_cases ht : q.1 ≤ (t : ℝ) <;>
      by_cases hu : q.1 ≤ (u : ℝ) <;>
      simp_all [Set.mem_prod, NNReal.coe_min, Set.mem_Ioc, not_lt, not_le]
    linarith
  · simp [Set.mem_prod, hy]

set_option linter.unusedSectionVars false in
theorem coeff_memLp_top (e : Elementary F) : MemLp e.coeff ∞ P := by
  obtain ⟨C, hC⟩ := e.bounded_coeff
  exact memLp_top_of_bound
    (e.measurable_coeff.mono (F.le e.s) le_rfl).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem elementaryIntegral_inner (e d : Elementary F) :
    inner ℝ (elementaryIntegral W e) (elementaryIntegral W d) =
      ∫ ω, (e.coeff ω * W (rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top) ω) *
        (d.coeff ω * W (rectangle d.s d.t d.A d.measurableSet_A d.volume_A_ne_top) ω) ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [elementaryIntegral_ae W e, elementaryIntegral_ae W d] with ω he hd
  simp only [RCLike.inner_apply, conj_trivial, he, hd, mul_comm]


/-- Split the earlier rectangle at the later coefficient time. The past term
has zero mean against the later increment; the future term factors by independence. -/
theorem elementary_gram_ordered (hW : IsWhiteNoise P F W) (e d : Elementary F)
    (hed : e.s ≤ d.s) :
    inner ℝ (elementaryIntegral W e) (elementaryIntegral W d) =
      inner ℝ (elementaryClass P e) (elementaryClass P d) := by
  let h := rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top
  let k := rectangle d.s d.t d.A d.measurableSet_A d.volume_A_ne_top
  let pre := rectangle e.s (min e.t d.s) e.A e.measurableSet_A e.volume_A_ne_top
  let post := rectangle d.s e.t e.A e.measurableSet_A e.volume_A_ne_top
  let C : Ω → ℝ := fun ω => e.coeff ω * d.coeff ω
  have hrect : h = pre + post := rectangle_split e.s e.t d.s hed _ _ _
  have hpre : SupportedBefore d.s pre := by
    filter_upwards [rectangle_supportedBefore e.s (min e.t d.s) e.A
      e.measurableSet_A e.volume_A_ne_top] with q hq hq'
    exact hq (lt_of_le_of_lt (NNReal.coe_le_coe.mpr (min_le_right _ _)) hq')
  have hpost : SupportedAfter d.s post := rectangle_supportedAfter _ _ _ _ _
  have hk : SupportedAfter d.s k := rectangle_supportedAfter _ _ _ _ _
  have hCm : Measurable[F d.s] C :=
    (e.measurable_coeff.mono (F.mono hed) le_rfl).mul d.measurable_coeff
  have hCtop : MemLp C ∞ P := (coeff_memLp_top e).mul (coeff_memLp_top d)
  have hCpre : MemLp (fun ω => C ω * W pre ω) 2 P := hCtop.mul (Lp.memLp (W pre))
  have hCpost : MemLp (fun ω => C ω * W post ω) 2 P := hCtop.mul (Lp.memLp (W post))
  obtain ⟨X, hXm, hXa⟩ := hW.adapted d.s pre hpre
  have hXma : AEStronglyMeasurable X P := (hXm.mono (F.le d.s)).aestronglyMeasurable
  have hvanish : (∫ ω, (C ω * W pre ω) * W k ω ∂P) = 0 := by
    calc
      _ = ∫ ω, (C ω * X ω) * W k ω ∂P := by
        apply integral_congr_ae
        filter_upwards [hXa] with ω hω
        rw [hω]
      _ = (∫ ω, C ω * X ω ∂P) * ∫ ω, W k ω ∂P :=
        (future_past_indep hW d.s (hCm.mul hXm.measurable)
          (future_measurable d.s k hk)).integral_fun_mul_eq_mul_integral
          (hCtop.aestronglyMeasurable.mul hXma) (Lp.aestronglyMeasurable _)
      _ = 0 := by rw [noise_mean_zero hW k, mul_zero]
  have hfuture : (∫ ω, (C ω * W post ω) * W k ω ∂P) =
      (∫ ω, C ω ∂P) * inner ℝ post k := by
    calc
      _ = ∫ ω, C ω * (W post ω * W k ω) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => mul_assoc _ _ _
      _ = (∫ ω, C ω ∂P) * ∫ ω, W post ω * W k ω ∂P :=
        (future_past_indep hW d.s hCm
          ((future_measurable d.s post hpost).mul (future_measurable d.s k hk))).integral_fun_mul_eq_mul_integral hCtop.aestronglyMeasurable
            ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _))
      _ = _ := by rw [noise_inner hW post k]
  rw [elementaryIntegral_inner, elementary_inner_factor]
  change (∫ ω, (e.coeff ω * W h ω) * (d.coeff ω * W k ω) ∂P) =
    (∫ ω, C ω ∂P) * inner ℝ h k
  calc
    _ = ∫ ω, (C ω * W pre ω) * W k ω + (C ω * W post ω) * W k ω ∂P := by
      have hs : W h = W pre + W post := by rw [hrect, map_add]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add (W pre) (W post)] with ω hω
      rw [hs, hω]
      change (e.coeff ω * (W pre ω + W post ω)) * (d.coeff ω * W k ω) = _
      dsimp [C]
      ring
    _ = (∫ ω, (C ω * W pre ω) * W k ω ∂P) +
        ∫ ω, (C ω * W post ω) * W k ω ∂P :=
      integral_add (hCpre.integrable_mul (Lp.memLp (W k)))
        (hCpost.integrable_mul (Lp.memLp (W k)))
    _ = _ := by
      rw [hvanish, hfuture, zero_add, hrect, inner_add_left]
      have hz : inner ℝ pre k = 0 := by
        rw [real_inner_comm]
        exact inner_eq_zero_of_supported d.s k pre hk hpre
      rw [hz, zero_add]

theorem elementary_gram (hW : IsWhiteNoise P F W) (e d : Elementary F) :
    inner ℝ (elementaryIntegral W e) (elementaryIntegral W d) =
      inner ℝ (elementaryClass P e) (elementaryClass P d) := by
  rcases le_total e.s d.s with hed | hde
  · exact elementary_gram_ordered hW e d hed
  · rw [real_inner_comm, elementary_gram_ordered hW d e hde, real_inner_comm]


/-- The isometric extension includes the corresponding interface random-elementary identification. -/
theorem exists_walshL2 (hW : IsWhiteNoise P F W) :
    ∃ I : PredL2 F P →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ e : Elementary F, I (elementaryClass P e) = elementaryIntegral W e := by
  classical
  let a := Finsupp.linearCombination ℝ (elementaryClass (F := F) P)
  let b := Finsupp.linearCombination ℝ (elementaryIntegral W (F := F))
  have hdense : DenseRange a := by
    change Dense (Set.range a)
    rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact dense_elementary
  have hnorm (x : Elementary F →₀ ℝ) : ‖b x‖ = ‖a x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [a, b, Finsupp.linearCombination_apply, Finsupp.sum,
      sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, elementary_gram hW]
  refine ⟨b.extendOfIsometry hdense hnorm, ?_⟩
  intro e
  simpa only [a, b, Finsupp.linearCombination_single, one_smul] using
    b.extendOfIsometry_eq hdense hnorm (Finsupp.single e 1)

/-- Select the isometric extension furnished by the existence theorem. -/
def walshL2 (hW : IsWhiteNoise P F W) : PredL2 F P →ₗᵢ[ℝ] Lp ℝ 2 P :=
  Classical.choose (exists_walshL2 hW)

/-- the corresponding interface identification certificate on every bounded random elementary term. -/
theorem walshL2_elementary (hW : IsWhiteNoise P F W) (e : Elementary F) :
    walshL2 hW (elementaryClass P e) = elementaryIntegral W e := by
  exact Classical.choose_spec (exists_walshL2 hW) e

/-- The Itô isometry is an equality of L² norms. -/
theorem norm_walshL2 (hW : IsWhiteNoise P F W) (G : PredL2 F P) :
    ‖walshL2 hW G‖ = ‖G‖ := by
  exact (walshL2 hW).norm_map G

/-- The same isometry as equality of real second-moment integrals. Both sides
are integrable squares, so this is not an equality of nonintegrable junk values. -/
theorem integral_sq_walshL2 (hW : IsWhiteNoise P F W) (G : PredL2 F P) :
    (∫ ω, (walshL2 hW G ω) ^ 2 ∂P) =
      ∫ q : ℝ × ℝ × Ω, (G.val q) ^ 2 ∂spaceTimeSample P := by
  have h := (walshL2 hW).inner_map_map G G
  simpa only [Submodule.coe_inner, L2.inner_def, RCLike.inner_apply,
    conj_trivial, ← sq] using h

/-- Random-elementary agreement uniquely determines any continuous linear extension. -/
theorem walshL2_unique (hW : IsWhiteNoise P F W)
    (J : PredL2 F P →L[ℝ] Lp ℝ 2 P)
    (hJ : ∀ e : Elementary F, J (elementaryClass P e) = elementaryIntegral W e) :
    J = (walshL2 hW).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext_on (dense_elementary (F := F) (P := P))
  rintro _ ⟨e, rfl⟩
  exact (hJ e).trans (walshL2_elementary hW e).symm

/-- The chosen measurable representative on the predictable finite-variance
domain, and the identically zero function outside that domain. -/
def walshT (hW : IsWhiteNoise P F W) (G : ℝ → ℝ → Ω → ℝ) : Ω → ℝ := by
  classical
  exact if hG : InDomain F P G then fun ω => walshL2 hW (toPredL2 G hG) ω else 0

/-- On its domain, totalization agrees almost surely with the L² operator. -/
theorem walshT_ae_eq (hW : IsWhiteNoise P F W) (G : ℝ → ℝ → Ω → ℝ)
    (hG : InDomain F P G) :
    walshT hW G =ᵐ[P] (fun ω => walshL2 hW (toPredL2 G hG) ω) := by
  simp only [walshT, dite_eq_left hG]
  exact Filter.EventuallyEq.rfl

/-- Outside the domain, totalization is literally zero. -/
theorem walshT_of_not_inDomain (hW : IsWhiteNoise P F W)
    (G : ℝ → ℝ → Ω → ℝ) (hG : ¬ InDomain F P G) : walshT hW G = 0 := by
  simp only [walshT, dite_eq_right hG]

/-- Additivity requires only the two input domains; their sum is in the domain
by `InDomain.add`. For a downstream application use the two kernel-weighted fields. -/
theorem walshT_add (hW : IsWhiteNoise P F W) (G G' : ℝ → ℝ → Ω → ℝ)
    (hG : InDomain F P G) (hG' : InDomain F P G') :
    walshT hW (fun s y ω => G s y ω + G' s y ω) =ᵐ[P]
      (fun ω => walshT hW G ω + walshT hW G' ω) := by
  have hclass : toPredL2 (fun s y ω => G s y ω + G' s y ω) (hG.add hG') =
      toPredL2 G hG + toPredL2 G' hG' := by
    apply Subtype.ext
    exact hG.memLp.toLp_add hG'.memLp
  simp only [walshT, dite_eq_left hG, dite_eq_left hG', dite_eq_left (hG.add hG'), hclass,
    map_add]
  exact Lp.coeFn_add _ _

/-- Real homogeneity on the domain, including the zero scalar. -/
theorem walshT_smul (hW : IsWhiteNoise P F W) (c : ℝ) (G : ℝ → ℝ → Ω → ℝ)
    (hG : InDomain F P G) :
    walshT hW (fun s y ω => c * G s y ω) =ᵐ[P]
      (fun ω => c * walshT hW G ω) := by
  have hclass : toPredL2 (fun s y ω => c * G s y ω) (hG.smul c) =
      c • toPredL2 G hG := by
    apply Subtype.ext
    exact hG.memLp.toLp_const_smul c
  simp only [walshT, dite_eq_left hG, dite_eq_left (hG.smul c), hclass, map_smul]
  exact Lp.coeFn_smul _ _

/-- Product-measure a.e. agreement identifies integrals of two domain inputs. -/
theorem walshT_congr_spaceTimeSample_ae (hW : IsWhiteNoise P F W)
    (G G' : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) (hG' : InDomain F P G')
    (heq : (fun q : ℝ × ℝ × Ω => G q.1 q.2.1 q.2.2) =ᵐ[spaceTimeSample P]
      (fun q : ℝ × ℝ × Ω => G' q.1 q.2.1 q.2.2)) :
    walshT hW G =ᵐ[P] walshT hW G' := by
  have hclass : toPredL2 G hG = toPredL2 G' hG' := by
    apply Subtype.ext
    exact MemLp.toLp_congr hG.memLp hG'.memLp heq
  exact (walshT_ae_eq hW G hG).trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun g => fun ω => walshL2 hW g ω)
      hclass)).trans (walshT_ae_eq hW G' hG').symm)

/-- Pointwise almost-sure agreement, with a null set allowed to depend on
`(s,y)`, gives pointwise almost-sure congruence via product-measure Fubini. -/
theorem walshT_congr_ae (hW : IsWhiteNoise P F W)
    (G G' : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) (hG' : InDomain F P G')
    (heq : ∀ s y, G s y =ᵐ[P] G' s y) :
    walshT hW G =ᵐ[P] walshT hW G' := by
  apply walshT_congr_spaceTimeSample_ae hW G G' hG hG'
  have hm := hG.1.mono (predictableSigma_le F) le_rfl
  have hm' := hG'.1.mono (predictableSigma_le F) le_rfl
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm hm')).mpr
  apply Filter.Eventually.of_forall
  intro s
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (hm.comp (measurable_const.prodMk measurable_id))
      (hm'.comp (measurable_const.prodMk measurable_id)))).mpr
  exact Filter.Eventually.of_forall (heq s)

/-- Restrict an integrand to `(0,t]`; for `t ≤ 0` this is the zero field. -/
def restrictTime (t : ℝ) (G : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ :=
  fun s y ω => (Set.Ioc 0 t).indicator (fun r => G r y ω) s

set_option linter.unusedSectionVars false in
/-- Time restriction preserves predictability and finite variance. -/
theorem InDomain.restrictTime {G : ℝ → ℝ → Ω → ℝ}
    (hG : InDomain F P G) (t : ℝ) : InDomain F P (restrictTime t G) := by
  let S : Set (ℝ × ℝ × Ω) := {q | q.1 ∈ Set.Ioc 0 t}
  have hS : MeasurableSet[predictableSigma F] S :=
    measurableSet_Ioc.preimage (measurable_coord F).fst
  have hm : Measurable[predictableSigma F]
      (fun q : ℝ × ℝ × Ω => Integral.restrictTime t G q.1 q.2.1 q.2.2) := by
    exact hG.1.indicator hS
  refine ⟨hm, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp
      (hG.memLp.indicator (predictableSigma_le F _ hS).nullMeasurableSet).integrable_sq.2

set_option linter.unusedVariables false in
/-- Causality needs only the domains of the restricted fields, not global
finite variance of the original fields. Agreement is exactly on `(0,t]`. -/
theorem walshT_causal (hW : IsWhiteNoise P F W) (t : ℝ)
    (G G' : ℝ → ℝ → Ω → ℝ)
    (hG : InDomain F P (restrictTime t G))
    (hG' : InDomain F P (restrictTime t G'))
    (heq : ∀ s ∈ Set.Ioc 0 t, ∀ y, G s y = G' s y) :
    walshT hW (restrictTime t G) =ᵐ[P] walshT hW (restrictTime t G') := by
  have he : restrictTime t G = restrictTime t G' := by
    funext s y ω
    by_cases hs : s ∈ Set.Ioc 0 t
    · simp only [restrictTime, Set.indicator_of_mem hs, heq s hs y]
    · simp only [restrictTime, Set.indicator_of_notMem hs]
  rw [he]

/-- If an integrand vanishes after `t` on positive time, restriction does not
change its integral. No condition is imposed on its nonpositive-time values. -/
theorem walshT_restrictTime (hW : IsWhiteNoise P F W) (t : ℝ)
    (G : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G)
    (hsupport : ∀ s y ω, 0 < s → t < s → G s y ω = 0) :
    walshT hW (restrictTime t G) =ᵐ[P] walshT hW G := by
  apply walshT_congr_spaceTimeSample_ae hW _ _ (hG.restrictTime t) hG
  have hpos : ∀ᵐ q ∂spaceTimeSample P, 0 < q.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_lt measurable_const measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Filter.Eventually.of_forall fun _ => hs
  filter_upwards [hpos] with q hq
  by_cases ht : q.1 ≤ t
  · exact Set.indicator_of_mem (show q.1 ∈ Set.Ioc 0 t from ⟨hq, ht⟩) _
  · rw [restrictTime, Set.indicator_of_notMem (by
      simpa only [Set.mem_Ioc, not_and] using fun _ => ht)]
    exact (hsupport _ _ _ hq (lt_of_not_ge ht)).symm

/-- The causal conclusion for supported kernel-weighted fields.
Apply to `K_{t,x} Φ` and `K_{t,x} Ψ`: the kernel vanishes for `s ≥ t`,
and agreement of `Φ, Ψ` on `(0,t]` supplies `heq`. All real `t` are allowed. -/
theorem walshT_causal_of_supported (hW : IsWhiteNoise P F W) (t : ℝ)
    (G G' : ℝ → ℝ → Ω → ℝ) (hG : InDomain F P G) (hG' : InDomain F P G')
    (hsupport : ∀ s y ω, 0 < s → t < s → G s y ω = 0)
    (hsupport' : ∀ s y ω, 0 < s → t < s → G' s y ω = 0)
    (heq : ∀ s ∈ Set.Ioc 0 t, ∀ y, G s y = G' s y) :
    walshT hW G =ᵐ[P] walshT hW G' := by
  exact (walshT_restrictTime hW t G hG hsupport).symm.trans
    ((walshT_causal hW t G G' (hG.restrictTime t) (hG'.restrictTime t) heq).trans
      (walshT_restrictTime hW t G' hG' hsupport'))

/-- The elementary stochastic integral is centred: the bounded `F s`-measurable
coefficient is independent of the increment on `(s,t] × A`, which has mean zero. -/
theorem integral_elementaryIntegral (hW : IsWhiteNoise P F W) (e : Elementary F) :
    ∫ ω, elementaryIntegral W e ω ∂P = 0 := by
  let h := rectangle e.s e.t e.A e.measurableSet_A e.volume_A_ne_top
  rw [integral_congr_ae (elementaryIntegral_ae W e),
    (future_past_indep hW e.s e.measurable_coeff
      (future_measurable e.s h (rectangle_supportedAfter _ _ _ _ _))).integral_fun_mul_eq_mul_integral
      (coeff_memLp_top e).aestronglyMeasurable (Lp.aestronglyMeasurable _),
    noise_mean_zero hW h, mul_zero]

set_option linter.unusedSectionVars false in
/-- On a probability space the expectation of an `L²` class is its inner product
with the constant one, so it is a continuous linear functional. -/
private theorem integral_eq_inner_const_one (f : Lp ℝ 2 P) :
    ∫ ω, f ω ∂P = inner ℝ (Lp.const 2 P (1 : ℝ)) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 P (1 : ℝ)] with ω hω
  rw [hω, Function.const_apply, RCLike.inner_apply, conj_trivial, mul_one]

/-- The Walsh integral of every predictable L² integrand has mean zero. The
expectation of the integral is a continuous linear functional on `PredL2`,
zero on elementary integrands, hence zero by density. -/
theorem integral_walshL2 (hW : IsWhiteNoise P F W) (G : PredL2 F P) :
    ∫ ω, walshL2 hW G ω ∂P = 0 := by
  let φ : PredL2 F P →L[ℝ] ℝ :=
    (innerSL ℝ (Lp.const 2 P (1 : ℝ))).comp (walshL2 hW).toContinuousLinearMap
  have hφ (G : PredL2 F P) : φ G = ∫ ω, walshL2 hW G ω ∂P :=
    (integral_eq_inner_const_one _).symm
  have hzero : φ = 0 := by
    apply ContinuousLinearMap.ext_on (dense_elementary (F := F) (P := P))
    rintro _ ⟨e, rfl⟩
    rw [hφ, walshL2_elementary hW e, integral_elementaryIntegral hW e,
      zero_apply]
  rw [← hφ, hzero, zero_apply]

/-- The totalized Walsh integral has mean zero for every field: on the domain it
agrees almost surely with `walshL2`, and off the domain it is identically zero. -/
theorem integral_walshT (hW : IsWhiteNoise P F W) (G : ℝ → ℝ → Ω → ℝ) :
    ∫ ω, walshT hW G ω ∂P = 0 := by
  by_cases hG : InDomain F P G
  · rw [integral_congr_ae (walshT_ae_eq hW G hG)]
    exact integral_walshL2 hW _
  · rw [walshT_of_not_inDomain hW G hG]
    simp

set_option linter.unusedSectionVars false in
/-- Every predictable L² class has a predictable representative, whose sample
sections `ω ↦ g (t, x, ω)` are then `F t`-measurable for every `t ≥ 0` and `x`. -/
theorem exists_adapted_representative (G : PredL2 F P) :
    ∃ g : ℝ × ℝ × Ω → ℝ, Measurable[predictableSigma F] g ∧
      (fun q => G.val q) =ᵐ[spaceTimeSample P] g ∧
      ∀ (t : ℝ≥0) (x : ℝ), Measurable[F t] (fun ω => g ((t : ℝ), x, ω)) := by
  have h := mem_lpMeas_iff_aestronglyMeasurable.mp G.prop
  exact ⟨h.mk _, h.stronglyMeasurable_mk.measurable, h.ae_eq_mk,
    fun t x => measurable_timeSection F h.stronglyMeasurable_mk.measurable t x⟩

end WalshIntegral.Integral
