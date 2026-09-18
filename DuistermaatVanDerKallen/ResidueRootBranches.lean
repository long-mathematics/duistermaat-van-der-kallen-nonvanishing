import DuistermaatVanDerKallen.ResidueCovering

/-! Locally unique smooth root branches, allowing both the fiber value and
all remaining coordinates to vary. No global ordering of roots is assumed. -/

open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- Include the fiber value among the implicit-function parameters. -/
def residueParameterEquation {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (q : (ℂ × (Fin d → ℂ)) × ℂ) : ℂ :=
  polynomialRootEquation (residueFiberPolynomial m u q.1.1) (q.1.2, q.2)

theorem residueParameterEquation_contDiff {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) : ContDiff ℂ ⊤ (residueParameterEquation m u) := by
  have hcons : ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ =>
      (Fin.cons q.2 q.1.2 : Fin (d + 1) → ℂ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (contDiff_snd : ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.2))
    · change ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.1.2 j)
      fun_prop
  have hc : ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.1.1) := by fun_prop
  convert (hc.mul ((mvPolynomial_contDiff (MvPolynomial.monomial m (1 : ℂ))).comp hcons)).sub
    ((mvPolynomial_contDiff u).comp hcons) using 1
  funext q
  simp [residueParameterEquation, polynomialRootEquation, residueFiberPolynomial,
    MvPolynomial.eval_monomial]

theorem residueParameterEquation_partial_isInvertible {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (q : (ℂ × (Fin d → ℂ)) × ℂ)
    (hq : MvPolynomial.eval (Fin.cons q.2 q.1.2)
      (MvPolynomial.pderiv 0 (residueFiberPolynomial m u q.1.1)) ≠ 0) :
    (fderiv ℂ (residueParameterEquation m u) q ∘L .inr ℂ (ℂ × (Fin d → ℂ)) ℂ).IsInvertible := by
  apply complexLinearMap_isInvertible
  have hd := (((residueParameterEquation_contDiff m u).differentiable (by simp)).differentiableAt
    (x := q)).hasFDerivAt
  have hg : HasDerivAt (fun z : ℂ => (q.1, z)) (0, 1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have he := (hd.comp_hasDerivAt q.2 hg).deriv
  have hp := (polynomialRootEquation_hasDerivAt (residueFiberPolynomial m u q.1.1)
    (q.1.2, q.2)).deriv
  change fderiv ℂ (residueParameterEquation m u) q (0, 1) ≠ 0
  rw [← he]
  exact hp ▸ hq

/-- Every simple root extends to a locally unique complex smooth branch in
both the fiber parameter and the remaining coordinates. -/
theorem exists_residue_root_branch {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (q : (ℂ × (Fin d → ℂ)) × ℂ)
    (hroot : residueParameterEquation m u q = 0)
    (hder : MvPolynomial.eval (Fin.cons q.2 q.1.2)
      (MvPolynomial.pderiv 0 (residueFiberPolynomial m u q.1.1)) ≠ 0) :
    ∃ ψ : ℂ × (Fin d → ℂ) → ℂ, ψ q.1 = q.2 ∧ ContDiffAt ℂ ⊤ ψ q.1 ∧
      (∀ᶠ b in 𝓝 q.1, residueParameterEquation m u (b, ψ b) = 0) ∧
      (∀ᶠ v in 𝓝 q, residueParameterEquation m u v = 0 ↔ ψ v.1 = v.2) := by
  have hc := (residueParameterEquation_contDiff m u).contDiffAt (x := q)
  have hi := residueParameterEquation_partial_isInvertible m u q hder
  refine ⟨hc.implicitFunction (by simp) hi, hc.implicitFunction_apply_self (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi, ?_, ?_⟩
  · simpa [hroot] using hc.eventually_apply_implicitFunction (by simp) hi
  · simpa [hroot] using hc.eventually_apply_eq_iff_implicitFunction (by simp) hi


/-- The chosen compact covering has a local smooth root branch at every one
of its points, with no additional regularity hypothesis. -/
theorem exists_residue_covering_with_branches {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (hm : ∀ i, 0 < m i) (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCoveringMap (residueRootProjection m u ε s) ∧
      ∀ z : ResidueRootSpace m u ε s,
        ∃ ψ : ℂ × (Fin d → ℂ) → ℂ, ψ (s, z.val.1) = z.val.2 ∧
          ContDiffAt ℂ ⊤ ψ (s, z.val.1) ∧
          (∀ᶠ b in 𝓝 (s, z.val.1), residueParameterEquation m u (b, ψ b) = 0) ∧
          (∀ᶠ v in 𝓝 ((s, z.val.1), z.val.2),
            residueParameterEquation m u v = 0 ↔ ψ v.1 = v.2) := by
  obtain ⟨ε, hε, B, hgood⟩ := exists_residue_covering m hm u hu
  refine ⟨ε, hε, B, ?_⟩
  intro s hs
  obtain ⟨hcov, hreg⟩ := hgood s hs
  refine ⟨hcov, fun z => ?_⟩
  exact exists_residue_root_branch m u ((s, z.val.1), z.val.2)
    z.property.2.2 (hreg z).2.2

end
end DuistermaatVanDerKallen
