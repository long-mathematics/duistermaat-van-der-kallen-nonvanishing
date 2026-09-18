import DuistermaatVanDerKallen.IntegerSupportShear
import DuistermaatVanDerKallen.RealExponentChange
import DuistermaatVanDerKallen.PolynomialFactorization

/-! The full unimodular vertex chart. Integer separating weights and shears
replace rational density and primitive-vector basis extension in the manuscript.
The resulting coordinate change is an actual integral linear automorphism. -/

open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- A coordinate minimum is negative in every direction, and yields a polynomial
factor with nonzero constant coefficient after a unimodular exponent change. -/
theorem unimodular_vertex_chart {d : ℕ} (hd : 1 ≤ d) (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ interior (newtonPolytope f)) :
    ∃ E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ), ∃ m : Fin d → ℤ,
      (∀ i, 0 < m i) ∧ ∃ u : MvPolynomial (Fin d) ℂ, u.coeff 0 ≠ 0 ∧
        AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f =
          AddMonoidAlgebra.single (-m) 1 * polynomialLaurentHom u ∧
        (∀ n : ℕ, constantTerm ((AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f) ^ n) =
          constantTerm (f ^ n)) := by
  classical
  cases d with
  | zero => omega
  | succ d =>
    have hne : f ≠ 0 := by
      intro he
      rw [he] at hf
      simp [newtonPolytope] at hf
    have hs : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr (by
      intro he
      exact hne (AddMonoidAlgebra.coeff_injective he))
    obtain ⟨E, v, hv, hmin⟩ := exists_all_coordinate_minimum f.coeff.support hs
    let q := AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f
    have hqcoeff (a : Fin (d + 1) → ℤ) : q.coeff a = f.coeff (E.symm a) := by
      simp [q, AddMonoidAlgebra.coeff_mapDomainRingEquiv]
    have hqmin : ∀ a ∈ q.coeff.support, ∀ i, E v i ≤ a i := by
      intro a ha i
      have ham : E.symm a ∈ f.coeff.support := by
        rw [Finsupp.mem_support_iff, ← hqcoeff]
        exact Finsupp.mem_support_iff.mp ha
      by_cases he : E.symm a = v
      · have hea : a = E v := by simpa using congrArg E he
        rw [hea]
      · simpa using (hmin (E.symm a) ham he i).le
    have hqint : (0 : Fin (d + 1) → ℝ) ∈ interior (newtonPolytope q) :=
      origin_interior_reindex E f hf
    have hvneg : ∀ i, E v i < 0 := coordinate_minimum_neg q hqint (E v) hqmin
    obtain ⟨u, hu, huc⟩ := factor_at_coordinate_minimum q (E v) hqmin
    refine ⟨E, -(E v), (fun i => neg_pos.mpr (hvneg i)), u, ?_, ?_, ?_⟩
    · rw [huc, hqcoeff, E.symm_apply_apply]
      exact Finsupp.mem_support_iff.mp hv
    · simpa using hu
    · exact constantTerm_pow_reindex E.toAddEquiv f


/-- The remaining analytic target after face reduction and the vertex chart.
Full Newton interior is retained: the monomial factor alone does not imply
nonvanishing of any positive-power constant term. -/
def VertexMinimalNonvanishing : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ m : Fin d → ℤ, (∀ i, 0 < m i) →
    ∀ u : MvPolynomial (Fin d) ℂ, u.coeff 0 ≠ 0 →
      (0 : Fin d → ℝ) ∈ interior (newtonPolytope
        (AddMonoidAlgebra.single (-m) 1 * polynomialLaurentHom u)) →
      ∃ n : ℕ, 1 ≤ n ∧ constantTerm
        ((AddMonoidAlgebra.single (-m) 1 * polynomialLaurentHom u) ^ n) ≠ 0

/-- The full arbitrary-rank minimal theorem follows from its vertex-chart form;
the latter is an explicit unproved analytic premise. -/
theorem minimal_of_vertex_minimal (h : VertexMinimalNonvanishing) : MinimalNonvanishing := by
  apply minimal_of_interior_minimal
  intro d hd f hf
  obtain ⟨E, m, hm, u, hu0, hu, hct⟩ := unimodular_vertex_chart hd f hf
  have hnewton := origin_interior_reindex E f hf
  rw [hu] at hnewton
  obtain ⟨n, hn, hne⟩ := h d hd m hm u hu0 hnewton
  refine ⟨n, hn, ?_⟩
  rw [← hct n, hu]
  exact hne

/-- Exact equivalence with the original target, without asserting either side. -/
theorem minimal_iff_vertex_minimal : MinimalNonvanishing ↔ VertexMinimalNonvanishing := by
  refine ⟨?_, minimal_of_vertex_minimal⟩
  intro h d _ m _ u _ hf
  have hm := interior_subset hf
  apply h d _ _ hm
  intro he
  rw [he] at hm
  simp [newtonPolytope] at hm

end
end DuistermaatVanDerKallen
