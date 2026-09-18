import DuistermaatVanDerKallen.TorusCoefficients
import DuistermaatVanDerKallen.CoefficientSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The constant-term generating function as a normalized product-circle
Cauchy integral. This uses scalar Haar integration; comparison to oriented
logarithmic-form integration and residue cycles remains separate. -/

open MeasureTheory
namespace DuistermaatVanDerKallen
noncomputable section

theorem hasSum_geometric_cauchy {s z : ℂ} (hs : ‖z‖ < ‖s‖) :
    HasSum (fun n : ℕ => z ^ n / s ^ (n + 1)) (1 / (s - z)) := by
  have hs0 : s ≠ 0 := norm_pos_iff.mp ((norm_nonneg z).trans_lt hs)
  have hr : ‖z / s‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hs0)).mpr hs
  have hsum := (hasSum_geometric_of_norm_lt_one hr).mul_right s⁻¹
  convert hsum using 1
  · funext n
    rw [div_pow, pow_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [← mul_inv_rev]
    field_simp

/-- Dominated convergence justifies termwise coefficient extraction on a
product of circles at every nonzero coordinate radius. -/
theorem hasSum_constantTerm_torusCauchy {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ)
    (hr : ∀ i, r i ≠ 0) {s : ℂ} (hs : weightedCoefficientMass f r < ‖s‖) :
    HasSum (fun n : ℕ => constantTerm (f ^ n) / s ^ (n + 1))
      (∫ x, 1 / (s - laurentEval f (torusPoint r x)) ∂phaseTorusMeasure d) := by
  let C := weightedCoefficientMass f r
  have hC : 0 ≤ C := weightedCoefficientMass_nonneg f r
  have hs0 : 0 < ‖s‖ := hC.trans_lt hs
  have hratio : C / ‖s‖ < 1 := (div_lt_one hs0).mpr hs
  have hg : Summable (fun n : ℕ => (C / ‖s‖) ^ n / ‖s‖) :=
    (summable_geometric_of_lt_one (div_nonneg hC (norm_nonneg s)) hratio).div_const ‖s‖
  have he : ∀ n : ℕ,
      (∫ x, laurentEval f (torusPoint r x) ^ n / s ^ (n + 1) ∂phaseTorusMeasure d) =
        constantTerm (f ^ n) / s ^ (n + 1) := by
    intro n
    rw [integral_div, integral_torusLaurent_pow f r hr]
  simp_rw [← he]
  apply hasSum_integral_of_dominated_convergence
    (fun n (_ : PhaseTorus d) => (C / ‖s‖) ^ n / ‖s‖)
  · intro n
    exact (((torusLaurent_continuous f r).pow n).div_const _).aestronglyMeasurable
  · intro n
    filter_upwards [] with x
    rw [norm_div, norm_pow, norm_pow]
    calc
      _ ≤ C ^ n / ‖s‖ ^ (n + 1) := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_torusLaurent_le_weightedMass f r x) n) (by positivity)
      _ = (C / ‖s‖) ^ n / ‖s‖ := by rw [div_pow, div_div, pow_succ]
  · exact Filter.Eventually.of_forall (fun _ => hg)
  · exact integrable_const _
  · filter_upwards [] with x
    exact hasSum_geometric_cauchy ((norm_torusLaurent_le_weightedMass f r x).trans_lt hs)

theorem generatingFunction_eq_torusCauchy {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ)
    (hr : ∀ i, r i ≠ 0) {s : ℂ} (hs : weightedCoefficientMass f r < ‖s‖) :
    constantTermGeneratingFunction f s =
      ∫ x, 1 / (s - laurentEval f (torusPoint r x)) ∂phaseTorusMeasure d :=
  (hasSum_constantTerm_torusCauchy f r hr hs).tsum_eq

end
end DuistermaatVanDerKallen
