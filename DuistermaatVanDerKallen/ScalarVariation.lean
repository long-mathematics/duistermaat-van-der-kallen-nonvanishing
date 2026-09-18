import DuistermaatVanDerKallen.RegularJacobian
import DuistermaatVanDerKallen.CountableSemialgebraic
import Mathlib.Topology.Algebra.Module.Determinant

/-! Uniform variation bounds for locally C¹ scalar semialgebraic families.
The source fibers are real line fibers, so no projection or Hardt input is
needed. Actual derivatives and measurable source sets are supplied. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

/-- In one real source dimension the graph fibers are already line fibers,
so the uniform Jacobian estimate needs no coordinate-projection premise. -/
theorem uniform_semialgebraic_scalar_variation
    {ι : Type*} (μ : Measure ℝ) [IsAddHaarMeasure μ]
    (E : (ι → ℝ) → Set ℝ) (hE : ∀ a, MeasurableSet (E a))
    (f d : (ι → ℝ) → ℝ → ℝ)
    (hgraph : IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ E (fun j => q (.inl (.inl j))) ∧
      f (fun j => q (.inl (.inl j))) (q (.inr ())) = q (.inl (.inr ()))})
    (hf : ∀ a, ∀ x ∈ E a, ContDiffAt ℝ 1 (f a) x)
    (hd : ∀ a, ∀ x ∈ E a, HasDerivAt (f a) (d a x) x) :
    ∃ N : ℕ, ∀ a, (∫⁻ x in E a, ENNReal.ofReal |d a x| ∂μ) ≤
      (N : ℝ≥0∞) * μ (f a '' E a) := by
  obtain ⟨N, hN⟩ := hgraph.uniform_finite_line_fibers
  refine ⟨N, fun a => ?_⟩
  let D (x : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (d a x)
  have hD (x : ℝ) (hx : x ∈ E a) : HasFDerivAt (f a) (D x) x := hd a x hx
  have hc := ae_countable_fibers_of_contDiffAt μ (E a) (f a) D (hf a) hD
  have hfinite (y : ℝ) (hy : ({x | x ∈ E a ∧ f a x = y}).Countable) :
      ({x | x ∈ E a ∧ f a x = y}).Finite :=
    hgraph.finite_line_fiber_of_countable (Sum.elim a (fun _ => y)) hy
  have hb := lintegral_abs_det_le_mul_image_of_contDiffAt μ (E a) (hE a) (f a) D
    (hf a) hD N (by
      filter_upwards [hc] with y hy
      exact ⟨hfinite y hy, hN (Sum.elim a (fun _ => y)) (hfinite y hy)⟩)
  simpa only [D, ContinuousLinearMap.det_toSpanSingleton] using hb

end
end DuistermaatVanDerKallen
