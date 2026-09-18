import DuistermaatVanDerKallen.ResidueDeformationCovering

/-! The exact sheet count, by a regular deformation to a monomial equation.
This implements the root-counting step without assuming a Rouché theorem. -/

namespace DuistermaatVanDerKallen
noncomputable section

def residueLeadingCoefficient {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (s : ℂ) (b : Fin d → ℂ) : ℂ :=
  s * ∏ j, b j ^ m j.succ

theorem eval_monomial_cons {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (s z : ℂ) (b : Fin d → ℂ) :
    MvPolynomial.eval (Fin.cons z b) (MvPolynomial.monomial m s) =
      residueLeadingCoefficient m s b * z ^ m 0 := by
  classical
  simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_succ,
    residueLeadingCoefficient, mul_left_comm, mul_comm]

theorem residueDeformationSlice_zero {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s z : ℂ) (b : Fin d → ℂ) :
    residueDeformationSlice m u s b (0, z) =
      residueLeadingCoefficient m s b * z ^ m 0 - MvPolynomial.eval (Fin.cons 0 b) u := by
  simp [residueDeformationSlice, residueDeformationEquation, eval_monomial_cons]

theorem residueDeformationSlice_one {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s z : ℂ) (b : Fin d → ℂ) :
    residueDeformationSlice m u s b (1, z) =
      polynomialRootEquation (residueFiberPolynomial m u s) (b, z) := by
  simp [residueDeformationSlice, residueDeformationEquation, polynomialRootEquation,
    residueFiberPolynomial]

namespace ResidueDiscData
variable {d : ℕ} {m : Fin (d + 1) →₀ ℕ} {u : MvPolynomial (Fin (d + 1)) ℂ}
variable (D : ResidueDiscData m u)

theorem leadingCoefficient_ne_zero {s : ℂ} (hs : D.threshold < ‖s‖)
    {b : Fin d → ℂ} (hb : ∀ i, ‖b i‖ = D.radius) : residueLeadingCoefficient m s b ≠ 0 := by
  apply mul_ne_zero (D.fiberValue_ne_zero hs)
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply pow_ne_zero
  exact norm_pos_iff.mp ((hb j).symm ▸ D.radius_pos)

theorem leadingCoefficient_radius_norm (s : ℂ) {b : Fin d → ℂ}
    (hb : ∀ i, ‖b i‖ = D.radius) :
    ‖residueLeadingCoefficient m s b‖ * D.radius ^ m 0 = ‖s‖ * D.monomialRadius := by
  simp only [residueLeadingCoefficient, norm_mul, norm_prod, norm_pow, hb,
    monomialRadius, Fin.prod_univ_succ]
  ring

theorem deformation_zero_card {s : ℂ} (hs : D.threshold < ‖s‖) (hm : 0 < m 0)
    {b : Fin d → ℂ} (hb : ∀ i, ‖b i‖ = D.radius) :
    Nat.card (compactRootProjection (residueDeformationSlice m u s b)
      residueDeformationDisc D.radius ⁻¹' {residueDeformationZero}) = m 0 := by
  rw [Nat.card_congr (compactRootFiberEquiv _ _ _ residueDeformationZero)]
  change Nat.card {z : ℂ // ‖z‖ ≤ D.radius ∧ residueDeformationSlice m u s b (0, z) = 0} = m 0
  simp_rw [residueDeformationSlice_zero, sub_eq_zero]
  have hzero : ∀ i : Fin (d + 1), ‖(Fin.cons (0 : ℂ) b : Fin (d + 1) → ℂ) i‖ ≤ D.radius := by
    intro i
    refine Fin.cases (by simpa using D.radius_pos.le) (fun j => (hb j).le) i
  apply complex_monomial_root_card_in_disc (m 0) hm _ _ (D.leadingCoefficient_ne_zero hs hb)
    (D.unit _ hzero) D.radius D.radius_pos
  rw [D.leadingCoefficient_radius_norm s hb]
  exact (D.eval_bound _ hzero).trans_lt (D.leading_bound hs)

/-- Every fiber of the original residue projection has exactly the positive
first monomial exponent many points. -/
theorem residueRootProjection_card {s : ℂ} (hs : D.threshold < ‖s‖) (hm : 0 < m 0)
    (b : residueCircleBase d D.radius) :
    Nat.card (residueRootProjection m u D.radius s ⁻¹' {b}) = m 0 := by
  unfold residueRootProjection
  rw [Nat.card_congr (compactRootFiberEquiv _ _ _ b)]
  have he := D.deformation_fiber_card_eq hs b.property
  rw [D.deformation_zero_card hs hm b.property,
    Nat.card_congr (compactRootFiberEquiv _ _ _ residueDeformationOne)] at he
  change m 0 = Nat.card {z : ℂ // ‖z‖ ≤ D.radius ∧
    residueDeformationSlice m u s b.val (1, z) = 0} at he
  simp_rw [residueDeformationSlice_one] at he
  exact he.symm


/-- The chosen disc also supplies the actual original covering charts. -/
theorem residueRoot_regular {s : ℂ} (hs : D.threshold < ‖s‖)
    (q : ResidueRootSpace m u D.radius s) :
    q.val.2 ≠ 0 ∧ ‖q.val.2‖ < D.radius ∧
      MvPolynomial.eval (Fin.cons q.val.2 q.val.1)
        (MvPolynomial.pderiv 0 (residueFiberPolynomial m u s)) ≠ 0 := by
  have hr : residueDeformationEquation m u s ((1, q.val.1), q.val.2) = 0 := by
    change residueDeformationSlice m u s q.val.1 (1, q.val.2) = 0
    rw [residueDeformationSlice_one]
    exact q.property.2.2
  obtain ⟨hnz, hi, hd⟩ := D.deformation_regular_root hs (by norm_num) q.property.2.1 q.property.1 hr
  refine ⟨hnz, hi, ?_⟩
  rw [← (polynomialRootEquation_hasDerivAt (residueFiberPolynomial m u s) q.val).deriv]
  change deriv (fun w => residueDeformationSlice m u s q.val.1 (1, w)) q.val.2 ≠ 0 at hd
  simpa only [residueDeformationSlice_one] using hd

theorem isCoveringMap_residueRootProjection {s : ℂ} (hs : D.threshold < ‖s‖) :
    IsCoveringMap (residueRootProjection m u D.radius s) := by
  apply isCoveringMap_compactRootProjection
    (hB := isCompact_residueCircleBase d D.radius)
    (hP := (polynomialRootEquation_contDiff _).continuous)
  intro q
  exact ⟨(D.residueRoot_regular hs q).2.1,
    (polynomialRootEquation_contDiff _).contDiffAt.of_le (by simp),
    polynomialRootEquation_partial_isInvertible _ _ (D.residueRoot_regular hs q).2.2⟩

theorem residueRootProjection_surjective {s : ℂ} (hs : D.threshold < ‖s‖) (hm : 0 < m 0) :
    Function.Surjective (residueRootProjection m u D.radius s) := by
  intro b
  have hp : 0 < Nat.card (residueRootProjection m u D.radius s ⁻¹' {b}) := by
    rw [D.residueRootProjection_card hs hm b]
    exact hm
  obtain ⟨q⟩ := (Nat.card_pos_iff.mp hp).1
  exact ⟨q.val, q.property⟩


theorem residueRootSpace_nonempty {s : ℂ} (hs : D.threshold < ‖s‖) (hm : 0 < m 0) :
    Nonempty (ResidueRootSpace m u D.radius s) := by
  let b : residueCircleBase d D.radius := ⟨fun _ => (D.radius : ℂ), by
    intro i
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.radius_pos]⟩
  obtain ⟨q, _⟩ := D.residueRootProjection_surjective hs hm b
  exact ⟨q⟩

/-- The roots counted by the degree theorem have the same local smooth branch
property, for this very choice of radius and threshold. -/
theorem residueRoot_local_branch {s : ℂ} (hs : D.threshold < ‖s‖)
    (q : ResidueRootSpace m u D.radius s) :
    ∃ ψ : ℂ × (Fin d → ℂ) → ℂ, ψ (s, q.val.1) = q.val.2 ∧
      ContDiffAt ℂ ⊤ ψ (s, q.val.1) ∧
      (∀ᶠ b in nhds (s, q.val.1), residueParameterEquation m u (b, ψ b) = 0) ∧
      (∀ᶠ v in nhds ((s, q.val.1), q.val.2), residueParameterEquation m u v = 0 ↔ ψ v.1 = v.2) :=
  exists_residue_root_branch m u ((s, q.val.1), q.val.2)
    q.property.2.2 (D.residueRoot_regular hs q).2.2

end ResidueDiscData

/-- The exact `m₁`-sheeted residue covering in every positive rank. The proof
uses a regular covering deformation to a monomial equation. -/
theorem exists_residue_covering_degree {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (hm : ∀ i, 0 < m i) (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCoveringMap (residueRootProjection m u ε s) ∧
      Function.Surjective (residueRootProjection m u ε s) ∧
      ∀ b : residueCircleBase d ε, Nat.card (residueRootProjection m u ε s ⁻¹' {b}) = m 0 := by
  obtain ⟨D⟩ := nonempty_residueDiscData m hm u hu
  exact ⟨D.radius, D.radius_pos, D.threshold, fun _ hs =>
    ⟨D.isCoveringMap_residueRootProjection hs,
      D.residueRootProjection_surjective hs (hm 0), D.residueRootProjection_card hs (hm 0)⟩⟩

end
end DuistermaatVanDerKallen
