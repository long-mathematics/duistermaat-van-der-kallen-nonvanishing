import DuistermaatVanDerKallen.ComplexSemialgebraic
import DuistermaatVanDerKallen.ResidueCoveringDegree

/-! The residue root locus is semialgebraic in the standard real coordinates.
Its exact equality with the coordinate image of the checked covering is proved. -/

namespace DuistermaatVanDerKallen
noncomputable section

theorem isComplexSemialgebraic_polynomial_root_locus {d : ℕ}
    (p : MvPolynomial (Fin d) ℂ) {ε : ℝ} (hε : 0 ≤ ε) (i : Fin d) :
    IsComplexSemialgebraic {z : Fin d → ℂ | (∀ j, ‖z j‖ ≤ ε) ∧
      (∀ j, j ≠ i → ‖z j‖ = ε) ∧ MvPolynomial.eval z p = 0} := by
  have hdisc := IsComplexSemialgebraic.forall_finite (fun j : Fin d => {z : Fin d → ℂ | ‖z j‖ ≤ ε})
    (fun j => IsComplexSemialgebraic.coord_norm_le j hε)
  have hcir := IsComplexSemialgebraic.forall_finite
    (fun j : {j : Fin d // j ≠ i} => {z : Fin d → ℂ | ‖z j.val‖ = ε})
    (fun j => IsComplexSemialgebraic.coord_norm_eq j.val hε)
  convert hdisc.inter (hcir.inter (IsComplexSemialgebraic.polynomial_zeroSet p)) using 1
  ext z
  simp

/-- The coordinate image of the covering is exactly the closed-disc root locus,
with every remaining coordinate on its prescribed circle. -/
theorem range_residueRootPoint_eq {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (ε : ℝ) (s : ℂ) :
    Set.range (residueRootPoint m u ε s) =
      {y : Fin (d + 1) → ℂ | (∀ j, ‖y j‖ ≤ ε) ∧
        (∀ j, j ≠ 0 → ‖y j‖ = ε) ∧ MvPolynomial.eval y (residueFiberPolynomial m u s) = 0} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨?_, ?_, q.property.2.2⟩
    · intro j
      refine Fin.cases q.property.2.1 (fun k => ?_) j
      exact (q.property.1 k).le
    · intro j
      refine Fin.cases (by simp) (fun k _ => ?_) j
      exact q.property.1 k
  · rintro ⟨hd, hc, hp⟩
    have hb : Fin.tail y ∈ residueCircleBase d ε := by
      intro j
      exact hc j.succ (Fin.succ_ne_zero j)
    let q : ResidueRootSpace m u ε s := ⟨(Fin.tail y, y 0), hb, hd 0, by
      simpa [polynomialRootEquation] using hp⟩
    refine ⟨q, ?_⟩
    exact Fin.cons_self_tail y

theorem isComplexSemialgebraic_range_residueRootPoint {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) {ε : ℝ} (hε : 0 ≤ ε) (s : ℂ) :
    IsComplexSemialgebraic (Set.range (residueRootPoint m u ε s)) := by
  rw [range_residueRootPoint_eq]
  exact isComplexSemialgebraic_polynomial_root_locus _ hε 0

/-- The actual residue construction has a compact semialgebraic coordinate
image and precisely the required number of sheets. This does not yet orient it
or turn it into a chain or cycle. -/
theorem exists_compact_semialgebraic_residue_covering {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (hm : ∀ i, 0 < m i) (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCompact (Set.range (residueRootPoint m u ε s)) ∧
      IsComplexSemialgebraic (Set.range (residueRootPoint m u ε s)) ∧
      IsCoveringMap (residueRootProjection m u ε s) ∧
      Function.Surjective (residueRootProjection m u ε s) ∧
      ∀ b : residueCircleBase d ε, Nat.card (residueRootProjection m u ε s ⁻¹' {b}) = m 0 := by
  obtain ⟨ε, hε, B, hgood⟩ := exists_residue_covering_degree m hm u hu
  exact ⟨ε, hε, B, fun s hs => ⟨isCompact_range_residueRootPoint m u ε s,
    isComplexSemialgebraic_range_residueRootPoint m u hε.le s, hgood s hs⟩⟩

/-- The total root equation, with the fiber value included as coordinate zero. -/
def residueFamilyPolynomial {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) : MvPolynomial (Fin (d + 2)) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (MvPolynomial.monomial m 1) -
    MvPolynomial.rename Fin.succ u

theorem eval_residueFamilyPolynomial {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s : ℂ) (y : Fin (d + 1) → ℂ) :
    MvPolynomial.eval (Fin.cons s y) (residueFamilyPolynomial m u) =
      MvPolynomial.eval y (residueFiberPolynomial m u s) := by
  simp [residueFamilyPolynomial, residueFiberPolynomial, MvPolynomial.eval_monomial,
    MvPolynomial.eval_rename, Function.comp_def]

/-- The entire root family over the complex fiber parameter has an explicit
semialgebraic description. No projection theorem is used. -/
theorem isComplexSemialgebraic_residueFamily {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsComplexSemialgebraic {q : Fin (d + 2) → ℂ |
      (∀ j : Fin (d + 1), ‖q j.succ‖ ≤ ε) ∧
      (∀ j : Fin (d + 1), j ≠ 0 → ‖q j.succ‖ = ε) ∧
      MvPolynomial.eval (Fin.tail q) (residueFiberPolynomial m u (q 0)) = 0} := by
  have hdisc := IsComplexSemialgebraic.forall_finite
    (fun j : Fin (d + 1) => {q : Fin (d + 2) → ℂ | ‖q j.succ‖ ≤ ε})
    (fun j => IsComplexSemialgebraic.coord_norm_le j.succ hε)
  have hcir := IsComplexSemialgebraic.forall_finite
    (fun j : {j : Fin (d + 1) // j ≠ 0} => {q : Fin (d + 2) → ℂ | ‖q j.val.succ‖ = ε})
    (fun j => IsComplexSemialgebraic.coord_norm_eq j.val.succ hε)
  have he (q : Fin (d + 2) → ℂ) : MvPolynomial.eval q (residueFamilyPolynomial m u) =
      MvPolynomial.eval (Fin.tail q) (residueFiberPolynomial m u (q 0)) := by
    simpa using eval_residueFamilyPolynomial m u (q 0) (Fin.tail q)
  convert hdisc.inter (hcir.inter (IsComplexSemialgebraic.polynomial_zeroSet (residueFamilyPolynomial m u))) using 1
  ext q
  simp [he]

end
end DuistermaatVanDerKallen
