import DuistermaatVanDerKallen.VertexChartEvaluation
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The small-polydisc estimates in the residue-cycle construction, and
nonvanishing of the coordinate derivatives of its polynomial fiber equation. -/

open Filter
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- The polynomial unit and every logarithmic partial satisfy the strict
small-polydisc estimate needed for the local residue construction. -/
theorem exists_polynomial_derivative_polydisc {d : ℕ} (u : MvPolynomial (Fin d) ℂ)
    (hu : u.coeff 0 ≠ 0) (m : Fin d → ℝ) (hm : ∀ i, 0 < m i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin d → ℂ, (∀ i, ‖y i‖ ≤ ε) →
      MvPolynomial.eval y u ≠ 0 ∧ ∀ i,
        ‖y i * MvPolynomial.eval y (MvPolynomial.pderiv i u)‖ < m i * ‖MvPolynomial.eval y u‖ := by
  have hu0 : MvPolynomial.eval (0 : Fin d → ℂ) u ≠ 0 := by
    simpa [MvPolynomial.eval_zero, MvPolynomial.constantCoeff] using hu
  have hunit : ∀ᶠ y : Fin d → ℂ in 𝓝 0, MvPolynomial.eval y u ≠ 0 :=
    (MvPolynomial.continuous_eval u).continuousAt.eventually_ne hu0
  have hder (i : Fin d) : ∀ᶠ y : Fin d → ℂ in 𝓝 0,
      ‖y i * MvPolynomial.eval y (MvPolynomial.pderiv i u)‖ < m i * ‖MvPolynomial.eval y u‖ := by
    apply (isOpen_lt (((continuous_apply i).mul (MvPolynomial.continuous_eval _)).norm)
      (continuous_const.mul (MvPolynomial.continuous_eval u).norm)).mem_nhds
    simpa using mul_pos (hm i) (norm_pos_iff.mpr hu0)
  have hgood := hunit.and (eventually_all.mpr hder)
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgood
  refine ⟨ε, hε, ?_⟩
  intro y hy
  apply hball
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg hε.le).mpr hy


/-- Formal partial derivatives agree with the analytic derivative when all
other polynomial coordinates are held fixed. -/
theorem mvPolynomial_hasDerivAt_update {d : ℕ} (u : MvPolynomial (Fin d) ℂ)
    (y : Fin d → ℂ) (i : Fin d) (z : ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update y i t) u)
      (MvPolynomial.eval (Function.update y i z) (MvPolynomial.pderiv i u)) z := by
  classical
  induction u using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const z c
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext t; simp
    · simp
  | mul_X p j hp =>
    by_cases hj : j = i
    · subst j
      convert hp.mul (hasDerivAt_id z) using 1
      · ext t; simp
      · simp [MvPolynomial.pderiv_X, mul_comm, add_comm]
    · simpa [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, hj, Ne.symm hj, mul_comm] using hp.mul_const (y j)

/-- The polynomial equation `s y^m - u(y) = 0` defining the local fiber roots. -/
def residueFiberPolynomial {d : ℕ} (m : Fin d →₀ ℕ) (u : MvPolynomial (Fin d) ℂ)
    (s : ℂ) : MvPolynomial (Fin d) ℂ := MvPolynomial.monomial m s - u

/-- The logarithmic derivative identity at every root of the fiber equation. -/
theorem residueFiberPolynomial_logderiv {d : ℕ} (m : Fin d →₀ ℕ)
    (u : MvPolynomial (Fin d) ℂ) (s : ℂ) (y : Fin d → ℂ)
    (hy : MvPolynomial.eval y (residueFiberPolynomial m u s) = 0) (i : Fin d) :
    y i * MvPolynomial.eval y (MvPolynomial.pderiv i (residueFiberPolynomial m u s)) =
      (m i : ℂ) * MvPolynomial.eval y u - y i * MvPolynomial.eval y (MvPolynomial.pderiv i u) := by
  have hroot : MvPolynomial.eval y (MvPolynomial.monomial m s) = MvPolynomial.eval y u := by
    simpa only [residueFiberPolynomial, map_sub, sub_eq_zero] using hy
  have hd := congrArg (MvPolynomial.eval y)
    (MvPolynomial.X_mul_pderiv_monomial (i := i) (m := m) (r := s))
  simp only [map_mul, MvPolynomial.eval_X, nsmul_eq_mul, map_natCast] at hd
  simp only [residueFiberPolynomial, map_sub, mul_sub]
  rw [hd, hroot]

/-- The strict derivative estimate excludes zero coordinates and vanishing
coordinate derivatives at roots; no root-counting theorem is assumed. -/
theorem residueFiberPolynomial_regular_root {d : ℕ} (m : Fin d →₀ ℕ)
    (u : MvPolynomial (Fin d) ℂ) (s : ℂ) (y : Fin d → ℂ)
    (hy : MvPolynomial.eval y (residueFiberPolynomial m u s) = 0) (i : Fin d)
    (hbound : ‖y i * MvPolynomial.eval y (MvPolynomial.pderiv i u)‖ <
      (m i : ℝ) * ‖MvPolynomial.eval y u‖) :
    y i ≠ 0 ∧ MvPolynomial.eval y (MvPolynomial.pderiv i (residueFiberPolynomial m u s)) ≠ 0 := by
  have hnum : (m i : ℂ) * MvPolynomial.eval y u -
      y i * MvPolynomial.eval y (MvPolynomial.pderiv i u) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    simp only [norm_mul, Complex.norm_natCast] at hn
    rw [norm_mul] at hbound
    exact (ne_of_lt hbound) hn.symm
  exact mul_ne_zero_iff.mp ((residueFiberPolynomial_logderiv m u s y hy i) ▸ hnum)

/-- The root regularity is for the actual one-variable analytic derivative,
not only a formal polynomial expression. -/
theorem residueFiberPolynomial_deriv_ne_zero {d : ℕ} (m : Fin d →₀ ℕ)
    (u : MvPolynomial (Fin d) ℂ) (s : ℂ) (y : Fin d → ℂ)
    (hy : MvPolynomial.eval y (residueFiberPolynomial m u s) = 0) (i : Fin d)
    (hbound : ‖y i * MvPolynomial.eval y (MvPolynomial.pderiv i u)‖ <
      (m i : ℝ) * ‖MvPolynomial.eval y u‖) :
    deriv (fun t => MvPolynomial.eval (Function.update y i t)
      (residueFiberPolynomial m u s)) (y i) ≠ 0 := by
  have hd := (mvPolynomial_hasDerivAt_update (residueFiberPolynomial m u s) y i (y i)).deriv
  simp only [Function.update_eq_self] at hd
  rw [hd]
  exact (residueFiberPolynomial_regular_root m u s y hy i hbound).2

/-- A single closed polydisc makes every fiber-equation root regular in each
coordinate, uniformly in the fiber value `s`. -/
theorem exists_residue_regular_polydisc {d : ℕ} (u : MvPolynomial (Fin d) ℂ)
    (hu : u.coeff 0 ≠ 0) (m : Fin d →₀ ℕ) (hm : ∀ i, 0 < m i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin d → ℂ, (∀ i, ‖y i‖ ≤ ε) →
      MvPolynomial.eval y u ≠ 0 ∧ ∀ s : ℂ,
        MvPolynomial.eval y (residueFiberPolynomial m u s) = 0 → ∀ i,
          y i ≠ 0 ∧ MvPolynomial.eval y (MvPolynomial.pderiv i (residueFiberPolynomial m u s)) ≠ 0 := by
  obtain ⟨ε, hε, hdisc⟩ := exists_polynomial_derivative_polydisc u hu
    (fun i => (m i : ℝ)) (fun i => by exact_mod_cast hm i)
  refine ⟨ε, hε, ?_⟩
  intro y hy
  obtain ⟨hunit, hbound⟩ := hdisc y hy
  exact ⟨hunit, fun s hs i => residueFiberPolynomial_regular_root m u s y hs i (hbound i)⟩

end
end DuistermaatVanDerKallen
