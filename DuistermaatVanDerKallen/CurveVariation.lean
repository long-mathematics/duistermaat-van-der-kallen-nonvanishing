import DuistermaatVanDerKallen.ScalarVariation

/-! Uniform Euclidean length bounds for given C¹ curve families whose
coordinate graphs are semialgebraic. The proof sums scalar variation estimates;
there is no coordinate-projection premise or assumed Lipschitz bound. The
source need not be compact. Constructing connecting curves and treating
general stratified arcs remain separate obligations. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

theorem euclidean_norm_le_sum_abs {κ : Type*} [Fintype κ]
    (v : EuclideanSpace ℝ κ) : ‖v‖ ≤ ∑ i, |v i| := by
  classical
  have he : (∑ i, PiLp.single 2 i (v i)) = v := by
    ext j
    simp
  calc
    ‖v‖ = ‖∑ i, PiLp.single 2 i (v i)‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖(PiLp.single 2 i (v i) : EuclideanSpace ℝ κ)‖ :=
      norm_sum_le Finset.univ (fun i => (PiLp.single 2 i (v i) : EuclideanSpace ℝ κ))
    _ = ∑ i, |v i| := by simp [PiLp.norm_single, Real.norm_eq_abs]

theorem uniform_semialgebraic_curve_variation
    {ι κ : Type*} [Fintype κ]
    (E : (ι → ℝ) → Set ℝ) (hE : ∀ a, MeasurableSet (E a))
    (γ v : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ E (fun j => q (.inl (.inl j))) ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hγ : ∀ a, ∀ t ∈ E a, ContDiffAt ℝ 1 (γ a) t)
    (hv : ∀ a, ∀ t ∈ E a, HasDerivAt (γ a) (v a t) t) :
    ∃ N : κ → ℕ, ∀ a, (∫⁻ t in E a, ENNReal.ofReal ‖v a t‖) ≤
      ∑ i, (N i : ℝ≥0∞) * volume ((fun t => γ a t i) '' E a) := by
  classical
  let π (i : κ) : EuclideanSpace ℝ κ →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) i
  have hcγ (i : κ) (a) (t) (ht : t ∈ E a) :
      ContDiffAt ℝ 1 (fun t => γ a t i) t :=
    (π i).contDiff.contDiffAt.comp t (hγ a t ht)
  have hcv (i : κ) (a) (t) (ht : t ∈ E a) :
      HasDerivAt (fun t => γ a t i) (v a t i) t :=
    (π i).hasFDerivAt.comp_hasDerivAt t (hv a t ht)
  choose N hN using fun i => uniform_semialgebraic_scalar_variation volume E hE
    (fun a t => γ a t i) (fun a t => v a t i) (hgraph i) (hcγ i) (hcv i)
  refine ⟨N, fun a => ?_⟩
  have hcont : ContinuousOn (v a) (E a) := by
    have hh : ContinuousOn (deriv (γ a)) (E a) := fun t ht =>
      (((hγ a t ht).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).continuousWithinAt
    exact hh.congr (fun t ht => (hv a t ht).deriv.symm)
  have hmeas (i : κ) : AEMeasurable (fun t => ENNReal.ofReal |v a t i|)
      (volume.restrict (E a)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((π i).continuous.comp_continuousOn hcont).abs).aemeasurable (hE a)
  calc
    (∫⁻ t in E a, ENNReal.ofReal ‖v a t‖) ≤
        ∫⁻ t in E a, ∑ i, ENNReal.ofReal |v a t i| := by
      apply lintegral_mono
      intro t
      change ENNReal.ofReal ‖v a t‖ ≤ ∑ i, ENNReal.ofReal |v a t i|
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (v a t i))]
      exact ENNReal.ofReal_le_ofReal (euclidean_norm_le_sum_abs (v a t))
    _ = ∑ i, ∫⁻ t in E a, ENNReal.ofReal |v a t i| :=
      lintegral_finsetSum' Finset.univ (fun i _ => hmeas i)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hN i a)


/-- The multiplicity constant is chosen before both the family parameter and
its bounding radius. The source set need not be compact or connected. -/
theorem uniform_semialgebraic_curve_length_bound
    {ι κ : Type*} [Fintype κ]
    (E : (ι → ℝ) → Set ℝ) (hE : ∀ a, MeasurableSet (E a))
    (γ v : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ E (fun j => q (.inl (.inl j))) ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hγ : ∀ a, ∀ t ∈ E a, ContDiffAt ℝ 1 (γ a) t)
    (hv : ∀ a, ∀ t ∈ E a, HasDerivAt (γ a) (v a t) t) :
    ∃ N : ℕ, ∀ a B, (∀ t ∈ E a, ‖γ a t‖ ≤ B) →
      (∫⁻ t in E a, ENNReal.ofReal ‖v a t‖) ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (2 * B) := by
  classical
  obtain ⟨N, hN⟩ := uniform_semialgebraic_curve_variation E hE γ v hgraph hγ hv
  refine ⟨∑ i, N i, fun a B hB => (hN a).trans ?_⟩
  have himg (i : κ) : (fun t => γ a t i) '' E a ⊆ Icc (-B) B := by
    rintro y ⟨t, ht, rfl⟩
    have hb : |γ a t i| ≤ B := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (γ a t) i).trans (hB t ht)
    exact abs_le.mp hb
  calc
    (∑ i, (N i : ℝ≥0∞) * volume ((fun t => γ a t i) '' E a)) ≤
        ∑ i, (N i : ℝ≥0∞) * ENNReal.ofReal (2 * B) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_right
      calc
        volume ((fun t => γ a t i) '' E a) ≤ volume (Icc (-B) B) := measure_mono (himg i)
        _ = ENNReal.ofReal (2 * B) := by rw [Real.volume_Icc]; congr 1; ring
    _ = _ := by rw [← Finset.sum_mul]; simp

/-- Bounded C¹ semialgebraic curve families have an actual integrable velocity
and uniformly bounded real length, not merely a bound on a formal integral. -/
theorem uniform_semialgebraic_curve_finite_length
    {ι κ : Type*} [Fintype κ]
    (E : (ι → ℝ) → Set ℝ) (hE : ∀ a, MeasurableSet (E a))
    (γ v : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ E (fun j => q (.inl (.inl j))) ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hγ : ∀ a, ∀ t ∈ E a, ContDiffAt ℝ 1 (γ a) t)
    (hv : ∀ a, ∀ t ∈ E a, HasDerivAt (γ a) (v a t) t)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ a, ∀ t ∈ E a, ‖γ a t‖ ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a, IntegrableOn (v a) (E a) ∧
      (∫ t in E a, ‖v a t‖) ≤ L := by
  obtain ⟨N, hN⟩ := uniform_semialgebraic_curve_length_bound E hE γ v hgraph hγ hv
  let L : ℝ := (N : ℝ) * (2 * B)
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg N) (by positivity)
  refine ⟨L, hL, fun a => ?_⟩
  have hb : (∫⁻ t in E a, ENNReal.ofReal ‖v a t‖) ≤ ENNReal.ofReal L := by
    simpa only [L, ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
      using hN a B (hbound a)
  have hcont : ContinuousOn (v a) (E a) := by
    have hh : ContinuousOn (deriv (γ a)) (E a) := fun t ht =>
      (((hγ a t ht).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).continuousWithinAt
    exact hh.congr (fun t ht => (hv a t ht).deriv.symm)
  have hi : IntegrableOn (v a) (E a) := by
    refine ⟨hcont.aestronglyMeasurable (hE a), ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi.norm
    (Filter.Eventually.of_forall (fun t => norm_nonneg (v a t)))
  rw [← he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hL).mp hb

end
end DuistermaatVanDerKallen
