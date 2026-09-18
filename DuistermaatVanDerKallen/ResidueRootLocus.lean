import DuistermaatVanDerKallen.ResiduePolydisc
import Mathlib.Analysis.Normed.Group.Bounded
/-! Compactness, boundary exclusion, and the Laurent interpretation of the local residue roots.
Root count and oriented cycles are separate obligations. -/

namespace DuistermaatVanDerKallen
noncomputable section
theorem exists_residue_boundary_bound {d : ℕ} (u : MvPolynomial (Fin d) ℂ) (m : Fin d →₀ ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ → ∀ y : Fin d → ℂ,
      (∀ i, ‖y i‖ = ε) → MvPolynomial.eval y (residueFiberPolynomial m u s) ≠ 0 := by
  classical
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin d → ℂ) ε).exists_bound_of_continuousOn
    (MvPolynomial.continuous_eval u).continuousOn
  let A : ℝ := m.prod (fun _ n => ε ^ n)
  have hA : 0 < A := Finset.prod_pos (fun _ _ => pow_pos hε _)
  refine ⟨C / A, ?_⟩
  intro s hs y hy he
  have hyn : y ∈ Metric.closedBall (0 : Fin d → ℂ) ε := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hε.le).mpr (fun i => (hy i).le)
  have heq : MvPolynomial.eval y (MvPolynomial.monomial m s) = MvPolynomial.eval y u := by
    simpa only [residueFiberPolynomial, map_sub, sub_eq_zero] using he
  have hn := congrArg norm heq
  simp only [MvPolynomial.eval_monomial, norm_mul, Finsupp.prod, norm_prod, norm_pow, hy] at hn
  have hlt : C < ‖s‖ * A := (div_lt_iff₀ hA).mp hs
  exact (not_lt_of_ge (hC y hyn)) (hn ▸ hlt)

theorem isCompact_residue_root_locus {d : ℕ} (u : MvPolynomial (Fin d) ℂ) (m : Fin d →₀ ℕ)
    (ε : ℝ) (i : Fin d) (s : ℂ) :
    IsCompact {y : Fin d → ℂ | (∀ j, ‖y j‖ ≤ ε) ∧
      (∀ j, j ≠ i → ‖y j‖ = ε) ∧
      MvPolynomial.eval y (residueFiberPolynomial m u s) = 0} := by
  have hdisc : IsCompact {y : Fin d → ℂ | ∀ j, ‖y j‖ ≤ ε} := by
    have heq : {y : Fin d → ℂ | ∀ j, ‖y j‖ ≤ ε} =
        Set.univ.pi (fun _ : Fin d => Metric.closedBall (0 : ℂ) ε) := by
      ext y
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [heq]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have hcircles : IsClosed {y : Fin d → ℂ | ∀ j, j ≠ i → ‖y j‖ = ε} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_iInter (fun _ : j ≠ i =>
      isClosed_eq (continuous_apply j).norm continuous_const))
  have hroot : IsClosed {y : Fin d → ℂ |
      MvPolynomial.eval y (residueFiberPolynomial m u s) = 0} :=
    isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  exact hdisc.inter_right (hcircles.inter hroot)


theorem exists_residue_interior_regular_roots {d : ℕ} (u : MvPolynomial (Fin d) ℂ) (hu : u.coeff 0 ≠ 0)
    (m : Fin d →₀ ℕ) (hm : ∀ i, 0 < m i) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ → ∀ i : Fin d,
      ∀ y : Fin d → ℂ, (∀ j, ‖y j‖ ≤ ε) → (∀ j, j ≠ i → ‖y j‖ = ε) →
      MvPolynomial.eval y (residueFiberPolynomial m u s) = 0 →
      (∀ j, y j ≠ 0) ∧ ‖y i‖ < ε ∧
      deriv (fun t => MvPolynomial.eval (Function.update y i t)
        (residueFiberPolynomial m u s)) (y i) ≠ 0 := by
  obtain ⟨ε, hε, hdisc⟩ := exists_polynomial_derivative_polydisc u hu
    (fun i => (m i : ℝ)) (fun i => by exact_mod_cast hm i)
  obtain ⟨B, hB⟩ := exists_residue_boundary_bound u m ε hε
  refine ⟨ε, hε, B, ?_⟩
  intro s hs i y hy hcir hroot
  have hbound := (hdisc y hy).2
  refine ⟨fun j => (residueFiberPolynomial_regular_root m u s y hroot j (hbound j)).1,
    lt_of_le_of_ne (hy i) ?_, residueFiberPolynomial_deriv_ne_zero m u s y hroot i (hbound i)⟩
  intro he
  apply hB s hs y _ hroot
  intro j
  by_cases hji : j = i
  · simpa [hji] using he
  · exact hcir j hji


theorem unimodular_vertex_chart_nat {d : ℕ} (hd : 1 ≤ d) (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ interior (newtonPolytope f)) :
    ∃ E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ), ∃ m : Fin d →₀ ℕ,
      (∀ i, 0 < m i) ∧ ∃ u : MvPolynomial (Fin d) ℂ, u.coeff 0 ≠ 0 ∧
        AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f =
          AddMonoidAlgebra.single (-natExponent m) 1 * polynomialLaurentHom u ∧
        (∀ n : ℕ, constantTerm ((AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f) ^ n) =
          constantTerm (f ^ n)) := by
  obtain ⟨E, m, hm, u, hu0, hu, hct⟩ := unimodular_vertex_chart hd f hf
  let mN : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (m i).toNat)
  have he : natExponent mN = m := by
    ext i
    change ((Finsupp.equivFunOnFinite.symm (fun i => (m i).toNat)) i : ℤ) = m i
    simp [Int.toNat_of_nonneg (hm i).le]
  refine ⟨E, mN, ?_, u, hu0, ?_, hct⟩
  · intro i
    change 0 < (Finsupp.equivFunOnFinite.symm (fun i => (m i).toNat)) i
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    have hi := hm i
    omega
  · rwa [he]


theorem residueFiberPolynomial_zero_iff {d : ℕ} (m : Fin d →₀ ℕ) (u : MvPolynomial (Fin d) ℂ)
    (s : ℂ) (y : Fin d → ℂ) (hy : ∀ i, y i ≠ 0) :
    MvPolynomial.eval y (residueFiberPolynomial m u s) = 0 ↔
      laurentEval (AddMonoidAlgebra.single (-natExponent m) 1 * polynomialLaurentHom u) y = s := by
  classical
  rw [laurentEval_polynomial_factor _ _ y hy]
  have hA : (∏ i, y i ^ m i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hy i))
  have hm : MvPolynomial.eval y (MvPolynomial.monomial m s) = s * ∏ i, y i ^ m i := by
    simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  have hi : (∏ i, y i ^ (-natExponent m) i) = (∏ i, y i ^ m i)⁻¹ := by
    simp [natExponent, zpow_neg, Finset.prod_inv_distrib]
  rw [hi]
  simp only [residueFiberPolynomial, map_sub, hm, sub_eq_zero]
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    field_simp at h
    simpa [mul_comm] using h.symm

end
end DuistermaatVanDerKallen
