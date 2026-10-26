module

public import Mathlib
public import WalshIntegral.GaussianSeries

@[expose] public section

/-!
# Space-time white noise relative to a filtration, Gaussian rectangle laws, and existence on raw and completed Gaussian product spaces.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace WalshIntegral.WhiteNoise

/-- Lebesgue time-space measure with time restricted to `(0, infinity)`.
Keeping the domain `ℝ × ℝ` avoids subtype coercions for elementary integrands
in this library. This product is the restriction of time-space Lebesgue measure to
positive time; values at nonpositive times are invisible in `Lp`. -/
def timeSpaceVolume : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ioi (0 : ℝ))).prod volume

/-- The real Hilbert space of deterministic square-integrable integrands. -/
abbrev H := Lp ℝ 2 timeSpaceVolume

/-- Essential support in `(0,t] × ℝ`, with respect to `timeSpaceVolume`. -/
def SupportedBefore (t : ℝ≥0) (h : H) : Prop :=
  ∀ᵐ z ∂timeSpaceVolume, (t : ℝ) < z.1 → h z = 0

/-- Essential support in `(s,infinity) × ℝ`, with respect to `timeSpaceVolume`. -/
def SupportedAfter (s : ℝ≥0) (h : H) : Prop :=
  ∀ᵐ z ∂timeSpaceVolume, z.1 ≤ (s : ℝ) → h z = 0

set_option backward.proofsInPublic true in
/-- The elementary deterministic rectangle as an actual `Lp` class.
No positivity or ordering assumption is needed to define the empty rectangle. -/
def rectangle (s t : ℝ≥0) (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) : H :=
  indicatorConstLp 2 (measurableSet_Ioc.prod hA) (by
    rw [timeSpaceVolume, Measure.prod_prod]
    apply ENNReal.mul_ne_top
    · exact ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _)
        (by simp : volume (Set.Ioc (s : ℝ) (t : ℝ)) < ∞))
    · exact hAfin) 1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The sigma-algebra generated jointly by all chosen future representatives.
An indexed supremum of comaps includes arbitrary finite joint observations. -/
@[instance_reducible]
def futureSigma (W : H →L[ℝ] Lp ℝ 2 P) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ h : {h : H // SupportedAfter s h},
    MeasurableSpace.comap (fun ω => W h.val ω) inferInstance

/-- The raw natural sigma-algebra of all chosen past representatives. -/
@[instance_reducible]
def pastSigma (W : H →L[ℝ] Lp ℝ 2 P) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ h : {h : H // SupportedBefore t h},
    MeasurableSpace.comap (fun ω => W h.val ω) inferInstance

/-- Completion of the natural filtration relative to the ambient measurable
space: an ambient measurable event belongs exactly when it agrees almost surely
with a raw past event. On a complete ambient probability space this is the full
augmentation by all subsets of ambient null sets. On the raw product space it
only includes ambient measurable null sets. This specifies the version
convention without identifying raw sigma-algebras of different representatives. -/
def IsCompletedNatural (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : H →L[ℝ] Lp ℝ 2 P) : Prop :=
  ∀ t S, MeasurableSet[F t] S ↔
    MeasurableSet S ∧ ∃ B, MeasurableSet[pastSigma W t] B ∧ S =ᵐ[P] B

/-- An isonormal Gaussian process compatible with `F` in the corrected the corresponding interface sense.
The Gaussian parameter is variance, not standard deviation. The final field
requires independence of the whole future sigma-algebra from `F s`. -/
structure IsWhiteNoise (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ) (W : H →L[ℝ] Lp ℝ 2 P) : Prop where
  isometry : Isometry W
  gaussian : ∀ h : H, P.map (fun ω => W h ω) = gaussianReal 0 (‖h‖₊ ^ 2)
  adapted : ∀ (t : ℝ≥0) (h : H), SupportedBefore t h →
    ∃ X : Ω → ℝ, StronglyMeasurable[F t] X ∧ X =ᵐ[P] (fun ω => W h ω)
  future_independent : ∀ s : ℝ≥0, Indep (futureSigma W s) (F s) P

variable [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {W : H →L[ℝ] Lp ℝ 2 P}

/-- The rectangle class represents the literal indicator, for use in this library. -/
theorem rectangle_ae (s t : ℝ≥0) (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) :
    (fun z => rectangle s t A hA hAfin z) =ᵐ[timeSpaceVolume]
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A).indicator (fun _ => (1 : ℝ)) := by
  exact indicatorConstLp_coeFn

/-- Rectangle increments have variance `(t-s) * volume A` in `ℝ≥0`.
Nonnegative time is encoded by `s t : ℝ≥0`; finite measure makes `toNNReal` exact. -/
theorem IsWhiteNoise.rectangle_law (hW : IsWhiteNoise P F W)
    (s t : ℝ≥0) (hst : s < t) (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) :
    P.map (fun ω => W (rectangle s t A hA hAfin) ω) =
      gaussianReal 0 ((t - s) * (volume A).toNNReal) := by
  rw [hW.gaussian]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_mul,
    NNReal.coe_sub hst.le]
  unfold rectangle
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (measureReal_nonneg)]
  norm_num
  rw [Measure.real, timeSpaceVolume, Measure.prod_prod, ENNReal.toReal_mul,
    Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioi]
  rw [max_eq_left s.coe_nonneg, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst.le))]
  rfl

/-- Every real linear combination of a finite family is centered Gaussian.
Its variance is the squared Hilbert norm, including the degenerate case. -/
theorem IsWhiteNoise.linear_combination_law (hW : IsWhiteNoise P F W)
    {n : ℕ} (h : Fin n → H) (a : Fin n → ℝ) :
    P.map (fun ω => ∑ i, a i * W (h i) ω) =
      gaussianReal 0 (‖∑ i, a i • h i‖₊ ^ 2) := by
  rw [← hW.gaussian]
  apply Measure.map_congr
  symm
  simp only [map_sum, map_smul]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => a i • W (h i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (W (h i)))] with ω hsum hsmul
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ => hsmul i

/-- The covariance matrix of any finite family is its Hilbert Gram matrix. -/
theorem IsWhiteNoise.covariance_eq_inner (hW : IsWhiteNoise P F W) (h g : H) :
    covariance (fun ω => W h ω) (fun ω => W g ω) P = inner ℝ h g := by
  have hmean (f : H) : ∫ ω, W f ω ∂P = 0 := by
    have heq := integral_id_gaussianReal (μ := 0) (v := ‖f‖₊ ^ 2)
    rw [← hW.gaussian f] at heq
    rw [integral_map (Lp.stronglyMeasurable (W f)).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x)
        (P.map (fun ω => W f ω)))] at heq
    exact heq
  let I : H →ₗᵢ[ℝ] Lp ℝ 2 P :=
    { W.toLinearMap with
      norm_map' := fun f => by
        change ‖W f‖ = ‖f‖
        simpa only [map_zero, dist_zero_right] using hW.isometry.dist_eq f 0 }
  rw [covariance_eq_sub (Lp.memLp (W h)) (Lp.memLp (W g)), hmean h, hmean g]
  have hi : inner ℝ (W h) (W g) = inner ℝ h g := I.inner_map_map h g
  simpa only [zero_mul, sub_zero, L2.inner_def, RCLike.inner_apply,
    conj_trivial, Pi.mul_apply, mul_comm] using hi

/-- A usable adapted representative, without claiming that the default `Lp`
representative is measurable for an arbitrary uncompleted filtration. -/
theorem IsWhiteNoise.exists_stronglyMeasurable_rep (hW : IsWhiteNoise P F W)
    (t : ℝ≥0) (h : H) (hh : SupportedBefore t h) :
    ∃ X : Ω → ℝ, StronglyMeasurable[F t] X ∧ X =ᵐ[P] (fun ω => W h ω) := by
  exact hW.adapted t h hh

/-- The complete future family is independent of the past filtration. -/
theorem IsWhiteNoise.futureSigma_indep (hW : IsWhiteNoise P F W) (s : ℝ≥0) :
    Indep (futureSigma W s) (F s) P := by
  exact hW.future_independent s

/-- A single future noise variable is independent of every event in `F s`. -/
theorem IsWhiteNoise.future_indep (hW : IsWhiteNoise P F W)
    (s : ℝ≥0) (h : H) (hh : SupportedAfter s h) :
    Indep (MeasurableSpace.comap (fun ω => W h ω) inferInstance) (F s) P := by
  exact indep_of_indep_of_le_left (hW.future_independent s)
    (le_iSup (fun k : {h : H // SupportedAfter s h} =>
      MeasurableSpace.comap (fun ω => W k.val ω) inferInstance) ⟨h, hh⟩)

/-- Joint independence of a finite future vector from `F s`; this does not
assert independence between the coordinates of that vector. -/
theorem IsWhiteNoise.future_fin_indep (hW : IsWhiteNoise P F W)
    (s : ℝ≥0) {n : ℕ} (h : Fin n → H) (hh : ∀ i, SupportedAfter s (h i)) :
    Indep (MeasurableSpace.comap (fun ω i => W (h i) ω)
      (inferInstance : MeasurableSpace (Fin n → ℝ))) (F s) P := by
  apply indep_of_indep_of_le_left (hW.future_independent s)
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  apply iSup_le
  intro i
  rw [MeasurableSpace.comap_comp]
  exact le_iSup_of_le ⟨h i, hh i⟩ le_rfl

/-- The isometry field gives the norm identity and rules out variance loss. -/
theorem IsWhiteNoise.norm_map (hW : IsWhiteNoise P F W) (h : H) :
    ‖W h‖ = ‖h‖ := by
  simpa only [map_zero, dist_zero_right] using hW.isometry.dist_eq h 0

/-- The deterministic Hilbert space is genuinely nontrivial. -/
theorem H_nontrivial : Nontrivial H := by
  let h : H := rectangle 0 1 (Set.Ioc 0 1) measurableSet_Ioc (by simp)
  have hnorm : ‖h‖ = 1 := by
    unfold h rectangle
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [timeSpaceVolume, Measure.real, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioi]
  exact ⟨⟨h, 0, fun heq => by simp [heq] at hnorm⟩⟩

/-- In particular the zero continuous linear map cannot be white noise. -/
theorem IsWhiteNoise.ne_zero (hW : IsWhiteNoise P F W) : W ≠ 0 := by
  have := H_nontrivial
  obtain ⟨h, hh⟩ := exists_ne (0 : H)
  intro hzero
  have hn := hW.norm_map h
  rw [hzero] at hn
  have : h = 0 := norm_eq_zero.mp (by simpa using hn.symm)
  exact hh this

omit [IsProbabilityMeasure P] in
/-- The raw past sigma-algebras are increasing. -/
theorem pastSigma_mono (W : H →L[ℝ] Lp ℝ 2 P) : Monotone (pastSigma W) := by
  intro s t hst
  unfold pastSigma
  apply iSup_le
  intro h
  have hh : SupportedBefore t h.val := by
    filter_upwards [h.property] with z hz htz
    exact hz (lt_of_le_of_lt (NNReal.coe_le_coe.mpr hst) htz)
  exact le_iSup_of_le ⟨h.val, hh⟩ le_rfl

omit [IsProbabilityMeasure P] in
/-- Raw past events are ambient measurable. -/
theorem pastSigma_le (W : H →L[ℝ] Lp ℝ 2 P) (t : ℝ≥0) : pastSigma W t ≤ mΩ := by
  apply iSup_le
  intro h
  exact (Lp.stronglyMeasurable (W h.val)).measurable.comap_le

/-- The natural filtration augmented by ambient measurable null modifications. -/
def completedNaturalFiltration (P : Measure Ω) (W : H →L[ℝ] Lp ℝ 2 P) :
    Filtration ℝ≥0 mΩ where
  seq t := mΩ ⊓ eventuallyMeasurableSpace (pastSigma W t) (ae P)
  mono' := by
    intro s t hst S hS
    obtain ⟨hS, B, hB, heq⟩ := hS
    exact ⟨hS, B, pastSigma_mono W hst B hB, heq⟩
  le' _ := inf_le_left

omit [IsProbabilityMeasure P] in
/-- The constructed filtration has exactly the stipulated relative completion. -/
theorem completedNaturalFiltration_spec (W : H →L[ℝ] Lp ℝ 2 P) :
    IsCompletedNatural P (completedNaturalFiltration P W) W := by
  intro t S
  rfl

omit [IsProbabilityMeasure P] in
/-- Each supported past representative is measurable for the augmented natural filtration. -/
theorem completedNaturalFiltration_adapted (W : H →L[ℝ] Lp ℝ 2 P)
    (t : ℝ≥0) (h : H) (hh : SupportedBefore t h) :
    StronglyMeasurable[completedNaturalFiltration P W t] (fun ω => W h ω) := by
  apply Measurable.stronglyMeasurable
  apply measurable_iff_comap_le.mpr
  apply le_inf (Lp.stronglyMeasurable (W h)).measurable.comap_le
  exact (le_iSup (fun k : {h : H // SupportedBefore t h} =>
    MeasurableSpace.comap (fun ω => W k.val ω) inferInstance) ⟨h, hh⟩).trans
      le_eventuallyMeasurableSpace

omit [IsProbabilityMeasure P] in
/-- Relative null augmentation preserves independence of sigma-algebras. -/
theorem indep_relative_completion {m₁ m₂ : MeasurableSpace Ω} (hi : Indep m₁ m₂ P) :
    Indep m₁ (mΩ ⊓ eventuallyMeasurableSpace m₂ (ae P)) P := by
  rw [Indep_iff] at hi ⊢
  intro A B hA hB
  obtain ⟨_, C, hC, heq⟩ := hB
  rw [measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ _) heq),
    measure_congr heq]
  exact hi A C hA hC

/-- Deterministic past and future subspaces are orthogonal. -/
theorem inner_eq_zero_of_supported (s : ℝ≥0) (h g : H)
    (hh : SupportedAfter s h) (hg : SupportedBefore s g) : inner ℝ h g = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hh, hg] with z hh hg
  by_cases hz : z.1 ≤ (s : ℝ)
  · simp [hh hz]
  · simp [hg (lt_of_not_ge hz)]

/-- Rectangles vanish beyond their upper time endpoint. -/
theorem rectangle_supportedBefore (s t : ℝ≥0) (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) : SupportedBefore t (rectangle s t A hA hAfin) := by
  filter_upwards [rectangle_ae s t A hA hAfin] with z hz htz
  rw [hz, Set.indicator_of_notMem]
  exact fun hmem => (not_le_of_gt htz) hmem.1.2

/-- Rectangles vanish at and before their lower time endpoint. -/
theorem rectangle_supportedAfter (s t : ℝ≥0) (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) : SupportedAfter s (rectangle s t A hA hAfin) := by
  filter_upwards [rectangle_ae s t A hA hAfin] with z hz hzs
  rw [hz, Set.indicator_of_notMem]
  exact fun hmem => (not_lt_of_ge hzs) hmem.1.1

set_option backward.proofsInPublic true in
/-- Unit time-space blocks form an infinite orthonormal sequence. -/
theorem orthonormal_unitRectangles : Orthonormal ℝ (fun n : ℕ =>
    rectangle n (n + 1) (Set.Ioc 0 1) measurableSet_Ioc (by simp)) := by
  let v : ℕ → H := fun n => rectangle n (n + 1) (Set.Ioc 0 1) measurableSet_Ioc (by simp)
  change Orthonormal ℝ v
  have hnorm (n : ℕ) : ‖v n‖ = 1 := by
    unfold v rectangle
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [timeSpaceVolume, Measure.real, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioi, max_eq_left (Nat.cast_nonneg n)]
  refine ⟨hnorm, ?_⟩
  have hortho (i j : ℕ) (hij : i < j) : inner ℝ (v j) (v i) = 0 := by
    apply inner_eq_zero_of_supported (i + 1)
    · have hj := rectangle_supportedAfter (j : ℝ≥0) (j + 1) (Set.Ioc 0 1)
        measurableSet_Ioc (by simp)
      filter_upwards [hj] with z hz hzi
      apply hz
      exact hzi.trans (by exact_mod_cast (Nat.add_one_le_iff.mpr hij))
    · exact rectangle_supportedBefore _ _ _ _ _
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · rw [real_inner_comm]
    exact hortho i j hij
  · exact hortho j i hij

/-- The deterministic integrand space has a Hilbert basis indexed by the natural numbers. -/
theorem H_has_nat_hilbertBasis : Nonempty (HilbertBasis ℕ ℝ H) := by
  have : SigmaFinite timeSpaceVolume := by unfold timeSpaceVolume; infer_instance
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology H := inferInstance
  exact exists_nat_hilbertBasis _ orthonormal_unitRectangles

/-- Covariance of an isometric centered Gaussian linear map. -/
theorem isonormal_covariance (W : H →L[ℝ] Lp ℝ 2 P) (hi : Isometry W)
    (hg : ∀ h : H, P.map (fun ω => W h ω) = gaussianReal 0 (‖h‖₊ ^ 2))
    (h g : H) : covariance (fun ω => W h ω) (fun ω => W g ω) P = inner ℝ h g := by
  have hmean (f : H) : ∫ ω, W f ω ∂P = 0 := by
    have hl : HasLaw (fun ω => W f ω) (gaussianReal 0 (‖f‖₊ ^ 2)) P :=
      ⟨(Lp.stronglyMeasurable (W f)).aemeasurable, hg f⟩
    simpa using hl.integral_eq
  let I : H →ₗᵢ[ℝ] Lp ℝ 2 P :=
    { W.toLinearMap with
      norm_map' := fun f => by
        change ‖W f‖ = ‖f‖
        simpa only [map_zero, dist_zero_right] using hi.dist_eq f 0 }
  rw [covariance_eq_sub (Lp.memLp (W h)) (Lp.memLp (W g)), hmean h, hmean g]
  have hi' : inner ℝ (W h) (W g) = inner ℝ h g := I.inner_map_map h g
  simpa only [zero_mul, sub_zero, L2.inner_def, RCLike.inner_apply,
    conj_trivial, Pi.mul_apply, mul_comm] using hi'

/-- A centered Gaussian isometry is white noise for its completed natural filtration. -/
theorem isWhiteNoise_completedNatural (W : H →L[ℝ] Lp ℝ 2 P) (hi : Isometry W)
    (hg : ∀ h : H, P.map (fun ω => W h ω) = gaussianReal 0 (‖h‖₊ ^ 2)) :
    IsWhiteNoise P (completedNaturalFiltration P W) W := by
  refine ⟨hi, hg, ?_, ?_⟩
  · intro t h hh
    exact ⟨fun ω => W h ω, completedNaturalFiltration_adapted W t h hh,
      Filter.EventuallyEq.refl _ _⟩
  · intro s
    apply indep_relative_completion
    have hproc := linearLp_isGaussianProcess W (fun h =>
      ⟨(Lp.stronglyMeasurable (W h)).aemeasurable, by rw [hg]; infer_instance⟩)
    let X : {h : H // SupportedAfter s h} → Ω → ℝ := fun h ω => W h.val ω
    let Y : {h : H // SupportedBefore s h} → Ω → ℝ := fun h ω => W h.val ω
    have hp : IsGaussianProcess (Sum.elim X Y) P := by
      convert hproc.comp_right (Sum.elim
        (fun h : {h : H // SupportedAfter s h} => h.val)
        (fun h : {h : H // SupportedBefore s h} => h.val)) using 1
      funext i
      cases i <;> rfl
    have hind := hp.indepFun_of_covariance_eq_zero
      (fun h => (Lp.stronglyMeasurable (W h.val)).aemeasurable)
      (fun h => (Lp.stronglyMeasurable (W h.val)).aemeasurable)
      (fun h g => (isonormal_covariance W hi hg h.val g.val).trans
        (inner_eq_zero_of_supported s h.val g.val h.property g.property))
    change Indep (MeasurableSpace.comap (fun ω h => X h ω) inferInstance)
      (MeasurableSpace.comap (fun ω h => Y h ω) inferInstance) P at hind
    simpa only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def, X, Y, futureSigma, pastSigma] using hind

/-- A Hilbert basis and independent standard Gaussian coordinates produce white noise. -/
theorem whiteNoise_of_basis_coordinates (e : HilbertBasis ℕ ℝ H) (ξ : ℕ → Lp ℝ 2 P)
    (hlaw : ∀ n, HasLaw (fun ω => ξ n ω) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun n ω => ξ n ω) P) :
    ∃ (F : Filtration ℝ≥0 mΩ) (W : H →L[ℝ] Lp ℝ 2 P),
      IsWhiteNoise P F W ∧ IsCompletedNatural P F W ∧
      ∀ h : H, Tendsto (fun N => ∑ n ∈ Finset.range N, (inner ℝ h (e n)) • ξ n)
        atTop (𝓝 (W h)) := by
  let J := orthonormalSeries ξ (orthonormal_gaussianLp ξ hlaw hind)
  let V := J.comp e.repr.toLinearIsometry
  let W := V.toContinuousLinearMap
  have hg (h : H) : P.map (fun ω => W h ω) = gaussianReal 0 (‖h‖₊ ^ 2) := by
    change P.map (fun ω => orthonormalSeries ξ (orthonormal_gaussianLp ξ hlaw hind)
      (e.repr h) ω) = _
    have heq := orthonormalSeries_gaussian_law ξ hlaw hind (e.repr h)
    simpa only [LinearIsometryEquiv.nnnorm_map] using heq
  refine ⟨completedNaturalFiltration P W, W,
    isWhiteNoise_completedNatural W V.isometry hg, completedNaturalFiltration_spec W, ?_⟩
  intro h
  have hlim := orthonormalSeries_tendsto ξ (orthonormal_gaussianLp ξ hlaw hind) (e.repr h)
  change Tendsto _ _ (𝓝 (orthonormalSeries ξ (orthonormal_gaussianLp ξ hlaw hind) (e.repr h)))
  simpa only [HilbertBasis.repr_apply_apply, real_inner_comm] using hlim

/-- The uncompleted countable product of standard Gaussian measures. -/
def productGaussian : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance productGaussian_isProbabilityMeasure : IsProbabilityMeasure productGaussian := by
  unfold productGaussian
  infer_instance

/-- The same sequence sample space with the completed product sigma-algebra.
`NullMeasurableSpace` is a type synonym, not a different set of outcomes. -/
abbrev CompletedSample := NullMeasurableSpace (ℕ → ℝ) productGaussian

/-- Full measure completion of the countable Gaussian product. -/
def completedProductGaussian : Measure CompletedSample := productGaussian.completion

instance completedProductGaussian_isProbabilityMeasure :
    IsProbabilityMeasure completedProductGaussian := by
  constructor
  change productGaussian Set.univ = 1
  exact measure_univ

/-- Any random sequence with the product Gaussian law supplies the required series witnesses. -/
theorem whiteNoise_of_product_law (X : Ω → ℕ → ℝ) (hX : HasLaw X productGaussian P) :
    ∃ (F : Filtration ℝ≥0 mΩ) (W : H →L[ℝ] Lp ℝ 2 P)
      (e : HilbertBasis ℕ ℝ H) (ξ : ℕ → Lp ℝ 2 P),
      IsWhiteNoise P F W ∧ IsCompletedNatural P F W ∧
      (∀ n, (fun ω => ξ n ω) =ᵐ[P] (fun ω => X ω n)) ∧
      ∀ h : H, Tendsto (fun N => ∑ n ∈ Finset.range N, (inner ℝ h (e n)) • ξ n)
        atTop (𝓝 (W h)) := by
  have hcoord (n : ℕ) : HasLaw (fun ω => X ω n) (gaussianReal 0 1) P := by
    have hl : HasLaw (fun ω : ℕ → ℝ => ω n) (gaussianReal 0 1) productGaussian :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).hasLaw
    exact hl.fun_comp hX
  have hm (n : ℕ) : MemLp (fun ω => X ω n) 2 P :=
    (hcoord n).memLp (memLp_id_gaussianReal' 2 (by norm_num))
  let ξ : ℕ → Lp ℝ 2 P := fun n => (hm n).toLp (fun ω => X ω n)
  have hae (n : ℕ) : (fun ω => ξ n ω) =ᵐ[P] (fun ω => X ω n) := (hm n).coeFn_toLp
  have hξlaw (n : ℕ) : HasLaw (fun ω => ξ n ω) (gaussianReal 0 1) P :=
    (hcoord n).congr (hae n)
  have hind : iIndepFun (fun n ω => X ω n) P := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun n => (hcoord n).aemeasurable)]
    simp_rw [(hcoord _).map_eq]
    exact hX.map_eq
  obtain ⟨e⟩ := H_has_nat_hilbertBasis
  obtain ⟨F, W, hW, hF, hsum⟩ := whiteNoise_of_basis_coordinates e ξ hξlaw
    (hind.congr fun n => (hae n).symm)
  exact ⟨F, W, e, ξ, hW, hF, hae, hsum⟩

/-- Existence already on the raw product space, with natural completion relative
to that ambient sigma-algebra. The coordinate representatives and Hilbert basis
are witnesses, not extra assumptions. Series convergence is in `Lp` for each h. -/
theorem exists_whiteNoise :
    ∃ (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (W : H →L[ℝ] Lp ℝ 2 productGaussian)
      (e : HilbertBasis ℕ ℝ H) (ξ : ℕ → Lp ℝ 2 productGaussian),
      IsWhiteNoise productGaussian F W ∧ IsCompletedNatural productGaussian F W ∧
      (∀ n, (fun ω => ξ n ω) =ᵐ[productGaussian] (fun ω => ω n)) ∧
      ∀ h : H, Tendsto (fun N => ∑ n ∈ Finset.range N, (inner ℝ h (e n)) • ξ n)
        atTop (𝓝 (W h)) := by
  exact whiteNoise_of_product_law id HasLaw.id

/-- Existence with the fully completed natural filtration on the completed
countable Gaussian product. Completion leaves probabilities and a.e. classes
unchanged, while admitting every subset of an ambient null set. -/
theorem exists_completed_whiteNoise :
    ∃ (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace CompletedSample))
      (W : H →L[ℝ] Lp ℝ 2 completedProductGaussian)
      (e : HilbertBasis ℕ ℝ H) (ξ : ℕ → Lp ℝ 2 completedProductGaussian),
      IsWhiteNoise completedProductGaussian F W ∧
      IsCompletedNatural completedProductGaussian F W ∧
      (∀ n, (fun ω => ξ n ω) =ᵐ[completedProductGaussian] (fun ω => ω n)) ∧
      ∀ h : H, Tendsto (fun N => ∑ n ∈ Finset.range N, (inner ℝ h (e n)) • ξ n)
        atTop (𝓝 (W h)) := by
  have hm : @Measurable CompletedSample (ℕ → ℝ)
      (inferInstance : MeasurableSpace CompletedSample)
      (inferInstance : MeasurableSpace (ℕ → ℝ)) (fun ω => ω) := by
    exact @Measurable.eventuallyMeasurable (ℕ → ℝ) inferInstance
      (ae productGaussian) inferInstance (ℕ → ℝ) inferInstance id measurable_id
  have hl : @HasLaw CompletedSample (ℕ → ℝ)
      (inferInstance : MeasurableSpace CompletedSample)
      (inferInstance : MeasurableSpace (ℕ → ℝ))
      (fun ω => ω) productGaussian completedProductGaussian := by
    refine ⟨hm.aemeasurable, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS]
    rfl
  exact whiteNoise_of_product_law (Ω := CompletedSample) (P := completedProductGaussian)
    (fun ω => ω) hl

end WalshIntegral.WhiteNoise
