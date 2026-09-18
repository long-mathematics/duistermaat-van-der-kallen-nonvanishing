import DuistermaatVanDerKallen.VertexChartEvaluation
import Mathlib.Analysis.SpecificLimits.Normed

/-! Convergence of the constant-term generating function, with an explicit
coefficient bound. No residue-cycle or period identity is asserted here. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- The finite coefficient mass, used only as an explicit scalar bound. -/
def coefficientMass {d : ℕ} (f : MultiLaurent d) : ℝ :=
  ∑ a ∈ f.coeff.support, ‖f.coeff a‖

theorem coefficientMass_nonneg {d : ℕ} (f : MultiLaurent d) : 0 ≤ coefficientMass f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem coeff_pow_norm_le {d : ℕ} (f : MultiLaurent d) (n : ℕ) (a : Fin d → ℤ) :
    ‖(f ^ n).coeff a‖ ≤ coefficientMass f ^ n := by
  classical
  induction n generalizing a with
  | zero =>
    by_cases ha : a = 0
    · simp [ha]
    · simp [AddMonoidAlgebra.one_def, ha]
  | succ n ih =>
    rw [pow_succ, AddMonoidAlgebra.coeff_mul_apply_right, Finsupp.sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ b ∈ f.coeff.support, coefficientMass f ^ n * ‖f.coeff b‖ := by
        apply Finset.sum_le_sum
        intro b _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (ih _) (norm_nonneg _)
      _ = coefficientMass f ^ (n + 1) := by
        rw [← Finset.mul_sum, pow_succ]
        rfl

theorem summable_constantTerm_series {d : ℕ} (f : MultiLaurent d) {s : ℂ}
    (hs : coefficientMass f < ‖s‖) :
    Summable (fun n : ℕ => constantTerm (f ^ n) / s ^ (n + 1)) := by
  have hs0 : 0 < ‖s‖ := (coefficientMass_nonneg f).trans_lt hs
  have hratio : coefficientMass f / ‖s‖ < 1 := (div_lt_one hs0).mpr hs
  have hgeom := (summable_geometric_of_lt_one
    (div_nonneg (coefficientMass_nonneg f) (norm_nonneg s)) hratio).div_const ‖s‖
  apply hgeom.of_norm_bounded
  intro n
  rw [norm_div, norm_pow]
  calc
    _ ≤ coefficientMass f ^ n / ‖s‖ ^ (n + 1) :=
      div_le_div_of_nonneg_right (coeff_pow_norm_le f n 0) (by positivity)
    _ = (coefficientMass f / ‖s‖) ^ n / ‖s‖ := by rw [div_pow, div_div, pow_succ]


/-- The scalar generating function appearing in the local residue lemma. -/
def constantTermGeneratingFunction {d : ℕ} (f : MultiLaurent d) (s : ℂ) : ℂ :=
  ∑' n : ℕ, constantTerm (f ^ n) / s ^ (n + 1)

/-- Universal positive-power vanishing forces the exact rational function. -/
theorem generatingFunction_eq_inv_of_vanishing {d : ℕ} (f : MultiLaurent d)
    (hf : ∀ n : ℕ, 1 ≤ n → constantTerm (f ^ n) = 0) (s : ℂ) :
    constantTermGeneratingFunction f s = 1 / s := by
  unfold constantTermGeneratingFunction
  rw [tsum_eq_single 0]
  · simp [constantTerm]
  · intro n hn
    rw [hf n (by omega), zero_div]

end
end DuistermaatVanDerKallen
