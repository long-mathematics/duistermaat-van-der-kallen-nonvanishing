import DuistermaatVanDerKallen.SemialgebraicCurveRegularity
import DuistermaatVanDerKallen.CurveRectifiability

/-! Uniform integrated-speed and metric-length bounds for bounded continuous
Euclidean curve families with semialgebraic coordinate graphs. Regularity
outside finitely many points is derived for each curve. Full graph fiber
counts bound variation uniformly without a uniform exceptional-point count.
This constructs neither the curves nor a Hardt trivialization. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory

theorem semialgebraic_curve_family_individual_graph
    {ι κ : Type*} [Fintype κ] (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (a : ι → ℝ) (i : κ) :
    IsSemialgebraic (Unit ⊕ Unit) {q | q (.inl ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ a (q (.inl ())) i = q (.inr ())} := by
  let p : ((ι ⊕ Unit) ⊕ Unit) → MvPolynomial (Unit ⊕ Unit) ℝ :=
    Sum.elim (Sum.elim (fun j => MvPolynomial.C (a j))
      (fun _ => MvPolynomial.X (.inr ()))) (fun _ => MvPolynomial.X (.inl ()))
  simpa [p] using (hgraph i).polynomial_preimage p

theorem continuous_semialgebraic_curve_family_finite_exceptions
    {ι κ : Type*} [Fintype κ] (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hc : ∀ a, ContinuousOn (γ a) (Icc (0 : ℝ) 1)) :
    ∃ T : (ι → ℝ) → Set ℝ, (∀ a, (T a).Finite) ∧
      ∀ a, ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ T a → ContDiffAt ℝ ⊤ (γ a) x := by
  have h (a : ι → ℝ) := continuous_semialgebraic_curve_smooth_outside_finite
    (γ a) (Ioo (0 : ℝ) 1) (semialgebraic_curve_family_individual_graph γ hgraph a)
    ((hc a).mono Ioo_subset_Icc_self)
  simp only [interior_Ioo] at h
  choose T hT hreg using h
  exact ⟨T, hT, hreg⟩


/-- The actual derivative is integrable on the full closed interval, including
all exceptional points, and its speed integral has a uniform bound. -/
theorem uniform_continuous_semialgebraic_finite_length
    {ι κ : Type*} [Fintype κ] (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hc : ∀ a, ContinuousOn (γ a) (Icc (0 : ℝ) 1))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ‖γ a t‖ ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a, IntegrableOn (deriv (γ a)) (Icc (0 : ℝ) 1) ∧
      (∫ t in Icc (0 : ℝ) 1, ‖deriv (γ a) t‖) ≤ L := by
  obtain ⟨T, hT, hreg⟩ := continuous_semialgebraic_curve_family_finite_exceptions γ hgraph hc
  have hr (a) (t) (ht : t ∈ Ioo (0 : ℝ) 1 \ T a) : ContDiffAt ℝ 1 (γ a) t :=
    (hreg a t ht.1 ht.2).of_le (by simp)
  obtain ⟨L, hL, hlen⟩ := uniform_semialgebraic_curve_finite_length_off_finite
    (fun _ => Ioo (0 : ℝ) 1) T (fun _ => measurableSet_Ioo) hT γ (fun a => deriv (γ a))
    hgraph hr (fun a t ht => (hr a t ht).differentiableAt_one.hasDerivAt)
    B hB (fun a t ht => hbound a t ht.1)
  refine ⟨L, hL, fun a => ?_⟩
  have he : Ioo (0 : ℝ) 1 \ T a =ᵐ[volume] Ioo (0 : ℝ) 1 :=
    sdiff_null_ae_eq_self ((hT a).measure_zero volume)
  constructor
  · rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact (integrableOn_congr_set_ae he).mp (hlen a).1
  · rw [integral_Icc_eq_integral_Ioo, ← setIntegral_congr_set he]
    exact (hlen a).2

/-- Uniform actual metric rectifiability of a bounded continuous semialgebraic
curve family. Smoothness, exceptional sets, and integrability are conclusions
of the construction, not premises. -/
theorem uniform_continuous_semialgebraic_rectifiable_curves
    {ι κ : Type*} [Fintype κ] (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hc : ∀ a, ContinuousOn (γ a) (Icc (0 : ℝ) 1))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ‖γ a t‖ ≤ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ a, BoundedVariationOn (γ a) (Icc (0 : ℝ) 1) ∧
      eVariationOn (γ a) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal L := by
  obtain ⟨L, _, hL⟩ := uniform_continuous_semialgebraic_finite_length γ hgraph hc B hB hbound
  obtain ⟨T, hT, hreg⟩ := continuous_semialgebraic_curve_family_finite_exceptions γ hgraph hc
  refine ⟨max 1 L, le_max_left _ _, fun a => ?_⟩
  have hb := eVariationOn_le_integral_speed_off_finite (γ a) (deriv (γ a)) (T a) (hT a)
    zero_le_one (hc a) (fun t ht hn =>
      ((hreg a t ht hn).differentiableAt (by simp)).hasDerivAt)
    (hL a).1
  have hh := hb.trans (ENNReal.ofReal_le_ofReal ((hL a).2.trans (le_max_right 1 L)))
  exact ⟨(hh.trans_lt ENNReal.ofReal_lt_top).ne, hh⟩

end
end DuistermaatVanDerKallen
