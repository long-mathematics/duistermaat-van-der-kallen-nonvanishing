import DuistermaatVanDerKallen.SemialgebraicBoundary
import DuistermaatVanDerKallen.BivariatePolynomials
import DuistermaatVanDerKallen.AlgebraicCurveRegularity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Continuous semialgebraic curves are smooth outside finitely many interior
parameter values. The exceptional set is constructed from the graph, not
assumed. Uniform family bounds and endpoint reparametrizations are not
asserted by these individual-curve results. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

theorem semialgebraic_scalar_polynomial_relation
    (f : ℝ → ℝ) (S : Set ℝ)
    (hgraph : IsSemialgebraic (Unit ⊕ Unit) {q | q (.inl ()) ∈ S ∧
      f (q (.inl ())) = q (.inr ())}) :
    ∃ P : Polynomial (Polynomial ℝ), P ≠ 0 ∧
      ∀ x ∈ S, bivariateEval P (x, f x) = 0 := by
  obtain ⟨p, hp, hroot⟩ := semialgebraic_scalar_graph_polynomial
    (fun x : Unit → ℝ => f (x ())) {x | x () ∈ S} hgraph
  refine ⟨bivariatePolynomialEquiv p, ?_, ?_⟩
  · exact (map_ne_zero_iff bivariatePolynomialEquiv bivariatePolynomialEquiv.injective).mpr hp
  · intro x hx
    rw [bivariateEval, eval_bivariatePolynomialEquiv]
    exact hroot (fun _ => x) hx

/-- A continuous semialgebraic scalar function is smooth at every interior
point of its domain except for a finite set. No smoothness of the original
parametrization, projection theorem, or Hardt theorem is a premise. -/
theorem continuous_semialgebraic_scalar_smooth_outside_finite
    (f : ℝ → ℝ) (S : Set ℝ)
    (hgraph : IsSemialgebraic (Unit ⊕ Unit) {q | q (.inl ()) ∈ S ∧
      f (q (.inl ())) = q (.inr ())})
    (hf : ContinuousOn f S) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x ∈ interior S, x ∉ E → ContDiffAt ℝ ⊤ f x := by
  obtain ⟨P, hP, hroot⟩ := semialgebraic_scalar_polynomial_relation f S hgraph
  exact continuous_algebraic_smooth_outside_finite P hP f (interior S) isOpen_interior
    (hf.mono interior_subset) (fun x hx => hroot x (interior_subset hx))

/-- Finite-dimensional coordinate graphs give one finite exceptional set for
the whole continuous curve. This bound is pointwise in the curve; no uniform
cardinality over a parameter family is asserted. -/
theorem continuous_semialgebraic_curve_smooth_outside_finite
    {κ : Type*} [Fintype κ] (γ : ℝ → EuclideanSpace ℝ κ) (S : Set ℝ)
    (hgraph : ∀ i, IsSemialgebraic (Unit ⊕ Unit) {q | q (.inl ()) ∈ S ∧
      γ (q (.inl ())) i = q (.inr ())})
    (hγ : ContinuousOn γ S) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x ∈ interior S, x ∉ E → ContDiffAt ℝ ⊤ γ x := by
  have hcoord (i : κ) := continuous_semialgebraic_scalar_smooth_outside_finite
    (fun t => γ t i) S (hgraph i) ((PiLp.continuous_apply 2 (fun _ : κ => ℝ) i).comp_continuousOn hγ)
  choose E hE hreg using hcoord
  refine ⟨⋃ i, E i, Set.finite_iUnion hE, ?_⟩
  intro x hx hxE
  apply contDiffAt_euclidean.mpr
  intro i
  exact hreg i x hx (fun hi => hxE (mem_iUnion.mpr ⟨i, hi⟩))

end
end DuistermaatVanDerKallen
