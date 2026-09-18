import DuistermaatVanDerKallen.ResidueRootLocus
import DuistermaatVanDerKallen.PolynomialRootCharts

/-! The actual compact regular covering of the product of the remaining
coordinate circles. Its nonemptiness and degree are not asserted here. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- The ordered base circles of the local residue construction. In rank one
this is the one-point empty product. -/
def residueCircleBase (d : ℕ) (ε : ℝ) : Set (Fin d → ℂ) := {b | ∀ i, ‖b i‖ = ε}

theorem isCompact_residueCircleBase (d : ℕ) (ε : ℝ) : IsCompact (residueCircleBase d ε) := by
  have he : residueCircleBase d ε = Set.univ.pi (fun _ : Fin d => Metric.sphere (0 : ℂ) ε) := by
    ext b
    simp [residueCircleBase]
  rw [he]
  exact isCompact_univ_pi (fun _ => isCompact_sphere _ _)

abbrev ResidueRootSpace {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :=
  CompactRootSpace (polynomialRootEquation (residueFiberPolynomial m u s))
    (residueCircleBase d ε) ε

def residueRootProjection {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :
    ResidueRootSpace m u ε s → residueCircleBase d ε :=
  compactRootProjection _ _ _

theorem compactSpace_residueRootSpace {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :
    CompactSpace (ResidueRootSpace m u ε s) :=
  compactSpace_compactRootSpace _ _ _ (isCompact_residueCircleBase d ε)
    (polynomialRootEquation_contDiff _).continuous

/-- Put a base point and its root back in the original ordered coordinates. -/
def residueRootPoint {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ)
    (z : ResidueRootSpace m u ε s) : Fin (d + 1) → ℂ := Fin.cons z.val.2 z.val.1

theorem residueRootPoint_continuous {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :
    Continuous (residueRootPoint m u ε s) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_subtype_val.snd
  · exact (continuous_apply j).comp continuous_subtype_val.fst

theorem residueRootPoint_injective {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :
    Function.Injective (residueRootPoint m u ε s) := by
  intro x y he
  have h := Fin.cons_inj.mp he
  exact Subtype.ext (Prod.ext h.2 h.1)

theorem isCompact_range_residueRootPoint {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :
    IsCompact (Set.range (residueRootPoint m u ε s)) := by
  let := compactSpace_residueRootSpace m u ε s
  exact isCompact_range (residueRootPoint_continuous m u ε s)

/-- The polynomial roots lie in the original Laurent fiber whenever their
coordinates are nonzero. -/
theorem residueRootSpace_laurent_fiber {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ)
    (z : ResidueRootSpace m u ε s)
    (hz : ∀ i : Fin (d + 1), (Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ) i ≠ 0) :
    laurentEval (AddMonoidAlgebra.single (-natExponent m) 1 * polynomialLaurentHom u)
      (Fin.cons z.val.2 z.val.1) = s :=
  (residueFiberPolynomial_zero_iff m u s _ hz).mp z.property.2.2

/-- The manuscript's root projection is an actual covering for all sufficiently
large fiber values. This theorem allows empty fibers; the degree calculation
and hence surjectivity remain separate obligations. -/
theorem exists_residue_covering {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (hm : ∀ i, 0 < m i) (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCoveringMap (residueRootProjection m u ε s) ∧
      ∀ z : ResidueRootSpace m u ε s,
        (∀ i : Fin (d + 1), (Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ) i ≠ 0) ∧ ‖z.val.2‖ < ε ∧
        MvPolynomial.eval (Fin.cons z.val.2 z.val.1)
          (MvPolynomial.pderiv 0 (residueFiberPolynomial m u s)) ≠ 0 := by
  obtain ⟨ε, hε, B, hgood⟩ := exists_residue_interior_regular_roots u hu m hm
  refine ⟨ε, hε, B, ?_⟩
  intro s hs
  have hroot (z : ResidueRootSpace m u ε s) := z.property.2.2
  have hz (z : ResidueRootSpace m u ε s) :
      (∀ i : Fin (d + 1), (Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ) i ≠ 0) ∧ ‖z.val.2‖ < ε ∧
      MvPolynomial.eval ((Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ))
        (MvPolynomial.pderiv 0 (residueFiberPolynomial m u s)) ≠ 0 := by
    have hall : ∀ i : Fin (d + 1), ‖(Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ) i‖ ≤ ε := by
      intro i
      refine Fin.cases z.property.2.1 (fun j => ?_) i
      exact (z.property.1 j).le
    have hcir : ∀ i : Fin (d + 1), i ≠ 0 → ‖(Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ) i‖ = ε := by
      intro i
      refine Fin.cases (by simp) (fun j _ => ?_) i
      exact z.property.1 j
    obtain ⟨hnz, hint, hd⟩ := hgood s hs 0 ((Fin.cons z.val.2 z.val.1 : Fin (d + 1) → ℂ)) hall hcir (hroot z)
    refine ⟨hnz, hint, ?_⟩
    rw [← (polynomialRootEquation_hasDerivAt (residueFiberPolynomial m u s) z.val).deriv]
    simpa [Fin.update_cons_zero, polynomialRootEquation] using hd
  refine ⟨?_, hz⟩
  apply isCoveringMap_compactRootProjection
    (hB := isCompact_residueCircleBase d ε)
    (hP := (polynomialRootEquation_contDiff _).continuous)
  intro z
  exact ⟨(hz z).2.1, (polynomialRootEquation_contDiff _).contDiffAt.of_le (by simp),
    polynomialRootEquation_partial_isInvertible _ _ (hz z).2.2⟩

/-- Every fiber of this compact covering is finite, without asserting its degree. -/
theorem finite_residueRootProjection_fiber {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ)
    (hcov : IsCoveringMap (residueRootProjection m u ε s)) (b : residueCircleBase d ε) :
    (residueRootProjection m u ε s ⁻¹' {b}).Finite := by
  let := compactSpace_residueRootSpace m u ε s
  have hc : IsCompact (residueRootProjection m u ε s ⁻¹' {b}) :=
    (isClosed_singleton.preimage hcov.continuous).isCompact
  exact hc.finite ⟨(hcov b).discreteTopology_fiber⟩

end
end DuistermaatVanDerKallen
