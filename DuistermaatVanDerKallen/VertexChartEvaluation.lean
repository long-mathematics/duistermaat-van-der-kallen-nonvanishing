import DuistermaatVanDerKallen.VertexChart
import DuistermaatVanDerKallen.LaurentEvaluation

/-! Pointwise evaluation of the checked vertex-chart factorization. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- Ordinary polynomial evaluation agrees with its Laurent inclusion, even at
points with zero coordinates because all exponents here are nonnegative. -/
theorem laurentEval_polynomialLaurentHom {d : ℕ} (u : MvPolynomial (Fin d) ℂ)
    (z : Fin d → ℂ) : laurentEval (polynomialLaurentHom u) z = MvPolynomial.eval z u := by
  change (Finsupp.mapDomain natExponent u.coeff).sum (fun a c => c * ∏ i, z i ^ a i) = _
  rw [Finsupp.sum_mapDomain_index (by intro a; simp) (by intro a c e; simp [add_mul])]
  rw [MvPolynomial.eval_eq']
  simp [Finsupp.sum, natExponent, MvPolynomial.support]

/-- A monomial factor in the Laurent algebra has the claimed pointwise value
on the open torus. -/
theorem laurentEval_polynomial_factor {d : ℕ} (v : Fin d → ℤ)
    (u : MvPolynomial (Fin d) ℂ) (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) :
    laurentEval (AddMonoidAlgebra.single v 1 * polynomialLaurentHom u) z =
      (∏ i, z i ^ v i) * MvPolynomial.eval z u := by
  rw [laurentEval_mul _ _ hz, laurentEval_polynomialLaurentHom]
  simp [laurentEval]

/-- The complete chart also gives the manuscript's evaluated formula, with a
polynomial nonvanishing at the origin and all power constant terms preserved. -/
theorem unimodular_vertex_chart_evaluation {d : ℕ} (hd : 1 ≤ d) (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ interior (newtonPolytope f)) :
    ∃ E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ), ∃ m : Fin d → ℤ,
      (∀ i, 0 < m i) ∧ ∃ u : MvPolynomial (Fin d) ℂ,
        MvPolynomial.eval (0 : Fin d → ℂ) u ≠ 0 ∧
        (∀ z : Fin d → ℂ, (∀ i, z i ≠ 0) →
          laurentEval (AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f) z =
            (∏ i, z i ^ (-m i)) * MvPolynomial.eval z u) ∧
        (∀ n : ℕ, constantTerm ((AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f) ^ n) =
          constantTerm (f ^ n)) := by
  obtain ⟨E, m, hm, u, hu0, hu, hct⟩ := unimodular_vertex_chart hd f hf
  refine ⟨E, m, hm, u, ?_, ?_, hct⟩
  · simpa [MvPolynomial.eval_zero, MvPolynomial.constantCoeff] using hu0
  · intro z hz
    rw [hu]
    exact laurentEval_polynomial_factor (-m) u z hz

end
end DuistermaatVanDerKallen
