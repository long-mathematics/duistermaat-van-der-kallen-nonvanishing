import DuistermaatVanDerKallen.CurveVariation
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Uniform metric rectifiability from coordinatewise semialgebraic
variation. Interior C¹ regularity and endpoint continuity suffice;
endpoint velocities need not be bounded. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory
open scoped ENNReal

/-- The metric variation is bounded by the actual integrated speed. Only
interior derivatives and continuity at the endpoints are required. -/
theorem eVariationOn_le_integral_speed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ v : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t)
    (hi : IntegrableOn v (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ ENNReal.ofReal (∫ t in Icc a b, ‖v t‖) := by
  have hint {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      IntervalIntegrable v volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
      (hi.mono_set (Icc_subset_Icc hx.1 hy.2))
  have hdist {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      ‖γ y - γ x‖ ≤ ∫ t in x..y, ‖v t‖ := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun t ht => hd t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩) (hint hx hy hxy)]
    exact intervalIntegral.norm_integral_le_integral_norm hxy
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hmem⟩
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), ‖v t‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (hdist (hmem i) (hmem (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∫ t in u 0..u n, ‖v t‖) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ => norm_nonneg _))]
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => (hint (hmem i) (hmem (i + 1)) (hu (Nat.le_succ i))).norm)]
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖v t‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hmem 0).1 (hu (Nat.zero_le n)) (hmem n).2
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi).norm
    _ = _ := by rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]


/-- A given bounded family of continuous semialgebraic curves, C¹ in the
interior, has a uniform rectifiable-length bound. The actual derivative is
used and may be unbounded near the endpoints. -/
theorem uniform_semialgebraic_rectifiable_curves
    {ι κ : Type*} [Fintype κ]
    (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hc : ∀ a, ContinuousOn (γ a) (Icc (0 : ℝ) 1))
    (hγ : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ 1 (γ a) t)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ‖γ a t‖ ≤ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ a, BoundedVariationOn (γ a) (Icc (0 : ℝ) 1) ∧
      eVariationOn (γ a) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal L := by
  obtain ⟨L, _, hL⟩ := uniform_semialgebraic_curve_finite_length
    (fun _ => Ioo (0 : ℝ) 1) (fun _ => measurableSet_Ioo) γ (fun a => deriv (γ a))
    hgraph hγ (fun a t ht => (hγ a t ht).differentiableAt_one.hasDerivAt) B hB hbound
  refine ⟨max 1 L, le_max_left _ _, fun a => ?_⟩
  have hi : IntegrableOn (deriv (γ a)) (Icc (0 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact (hL a).1
  have hb := eVariationOn_le_integral_speed (γ a) (deriv (γ a)) zero_le_one (hc a)
    (fun t ht => (hγ a t ht).differentiableAt_one.hasDerivAt) hi
  rw [integral_Icc_eq_integral_Ioo] at hb
  have hh := hb.trans (ENNReal.ofReal_le_ofReal ((hL a).2.trans (le_max_right 1 L)))
  exact ⟨(hh.trans_lt ENNReal.ofReal_lt_top).ne, hh⟩

end
end DuistermaatVanDerKallen
