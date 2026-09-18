import Mathlib.Analysis.Calculus.Deriv.Prod
import DuistermaatVanDerKallen.ResiduePolydisc
import DuistermaatVanDerKallen.CompactRootCovering

/-! Polynomial coordinate derivatives supply the local inverses used in the
compact residue covering. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- Evaluation of an ordinary multivariate polynomial is complex smooth. -/
theorem mvPolynomial_contDiff {d : ℕ} (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ ⊤ (fun y : Fin d → ℂ => MvPolynomial.eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℂ ⊤ (fun _ : Fin d → ℂ => c))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℂ ℂ i)

/-- The first polynomial coordinate is singled out as the root variable. -/
def polynomialRootEquation {d : ℕ} (p : MvPolynomial (Fin (d + 1)) ℂ)
    (q : (Fin d → ℂ) × ℂ) : ℂ := MvPolynomial.eval (Fin.cons q.2 q.1) p

theorem polynomialRootEquation_contDiff {d : ℕ} (p : MvPolynomial (Fin (d + 1)) ℂ) :
    ContDiff ℂ ⊤ (polynomialRootEquation p) := by
  apply (mvPolynomial_contDiff p).comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_snd : ContDiff ℂ ⊤ (fun q : (Fin d → ℂ) × ℂ => q.2))
  · simpa [Function.comp_def] using (contDiff_apply ℂ ℂ j).comp
      (contDiff_fst : ContDiff ℂ ⊤ (fun q : (Fin d → ℂ) × ℂ => q.1))

/-- A complex linear scalar map is invertible as soon as its value at one is nonzero. -/
theorem complexLinearMap_isInvertible {L : ℂ →L[ℂ] ℂ} (hL : L 1 ≠ 0) : L.IsInvertible := by
  have he (a : ℂ) : L a = a * L 1 := by
    simpa using L.map_smul a (1 : ℂ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · apply ContinuousLinearMap.ext
    intro a
    change L ((L 1)⁻¹ * a) = a
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro a
    change (L 1)⁻¹ * L a = a
    rw [he a]
    field_simp

/-- The selected partial derivative is the actual derivative in the root variable. -/
theorem polynomialRootEquation_hasDerivAt {d : ℕ} (p : MvPolynomial (Fin (d + 1)) ℂ)
    (q : (Fin d → ℂ) × ℂ) :
    HasDerivAt (fun z => polynomialRootEquation p (q.1, z))
      (MvPolynomial.eval (Fin.cons q.2 q.1) (MvPolynomial.pderiv 0 p)) q.2 := by
  simpa [Fin.update_cons_zero, polynomialRootEquation] using
    mvPolynomial_hasDerivAt_update p (Fin.cons q.2 q.1) 0 q.2

theorem polynomialRootEquation_partial_isInvertible {d : ℕ}
    (p : MvPolynomial (Fin (d + 1)) ℂ) (q : (Fin d → ℂ) × ℂ)
    (hq : MvPolynomial.eval (Fin.cons q.2 q.1) (MvPolynomial.pderiv 0 p) ≠ 0) :
    (fderiv ℂ (polynomialRootEquation p) q ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
  apply complexLinearMap_isInvertible
  have hd := (((polynomialRootEquation_contDiff p).differentiable (by simp)).differentiableAt (x := q)).hasFDerivAt
  have hg : HasDerivAt (fun z : ℂ => (q.1, z)) (0, 1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have he := (hd.comp_hasDerivAt q.2 hg).deriv
  have hp := (polynomialRootEquation_hasDerivAt p q).deriv
  change fderiv ℂ (polynomialRootEquation p) q (0, 1) ≠ 0
  rw [← he]
  exact hp ▸ hq

end
end DuistermaatVanDerKallen
