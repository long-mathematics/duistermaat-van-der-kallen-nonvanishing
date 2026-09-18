import DuistermaatVanDerKallen.ResidueRootBranches
/-! A deformation shrinking the first coordinate in the polynomial unit.
Its logarithmic derivative obeys the same strict polydisc estimate. -/

namespace DuistermaatVanDerKallen
noncomputable section

def residueDeformationEquation {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s : ℂ)
    (q : (ℂ × (Fin d → ℂ)) × ℂ) : ℂ :=
  MvPolynomial.eval (Fin.cons q.2 q.1.2) (MvPolynomial.monomial m s) -
    MvPolynomial.eval (Fin.cons (q.1.1 * q.2) q.1.2) u

theorem residueDeformationEquation_contDiff {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s : ℂ) :
    ContDiff ℂ ⊤ (residueDeformationEquation m u s) := by
  have hfirst : ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ =>
      (Fin.cons q.2 q.1.2 : Fin (d + 1) → ℂ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (contDiff_snd : ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.2))
    · change ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.1.2 j)
      fun_prop
  have hscale : ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ =>
      (Fin.cons (q.1.1 * q.2) q.1.2 : Fin (d + 1) → ℂ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.1.1 * q.2)
      fun_prop
    · change ContDiff ℂ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℂ => q.1.2 j)
      fun_prop
  exact ((mvPolynomial_contDiff (MvPolynomial.monomial m s)).comp hfirst).sub
    ((mvPolynomial_contDiff u).comp hscale)

theorem residueDeformationEquation_logderiv {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s t z : ℂ) (b : Fin d → ℂ)
    (hroot : residueDeformationEquation m u s ((t, b), z) = 0) :
    z * deriv (fun w => residueDeformationEquation m u s ((t, b), w)) z =
      (m 0 : ℂ) * MvPolynomial.eval (Fin.cons (t * z) b) u -
        (t * z) * MvPolynomial.eval (Fin.cons (t * z) b) (MvPolynomial.pderiv 0 u) := by
  have hm := polynomialRootEquation_hasDerivAt (MvPolynomial.monomial m s) (b, z)
  have hu := (polynomialRootEquation_hasDerivAt u (b, t * z)).comp z
    ((hasDerivAt_id z).const_mul t)
  have hh : HasDerivAt
      (fun w => polynomialRootEquation (MvPolynomial.monomial m s) (b, w) -
        polynomialRootEquation u (b, t * w))
      (MvPolynomial.eval (Fin.cons z b) (MvPolynomial.pderiv 0 (MvPolynomial.monomial m s)) -
        MvPolynomial.eval (Fin.cons (t * z) b) (MvPolynomial.pderiv 0 u) * t) z := by
    convert hm.sub hu using 1
    · ext w
      rfl
    · simp
  have hd := hh.deriv
  have he : MvPolynomial.eval (Fin.cons z b) (MvPolynomial.monomial m s) =
      MvPolynomial.eval (Fin.cons (t * z) b) u := by
    simpa only [residueDeformationEquation, sub_eq_zero] using hroot
  have hl := congrArg (MvPolynomial.eval (Fin.cons z b))
    (MvPolynomial.X_mul_pderiv_monomial (i := (0 : Fin (d + 1))) (m := m) (r := s))
  simp only [map_mul, MvPolynomial.eval_X, nsmul_eq_mul, map_natCast, Fin.cons_zero] at hl
  change z * deriv (fun w => polynomialRootEquation (MvPolynomial.monomial m s) (b, w) -
    polynomialRootEquation u (b, t * w)) z = _
  rw [hd, mul_sub, hl, he]
  ring

theorem residueDeformationEquation_regular_root {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s t z : ℂ) (b : Fin d → ℂ)
    (hroot : residueDeformationEquation m u s ((t, b), z) = 0)
    (hbound : ‖(t * z) * MvPolynomial.eval (Fin.cons (t * z) b) (MvPolynomial.pderiv 0 u)‖ <
      (m 0 : ℝ) * ‖MvPolynomial.eval (Fin.cons (t * z) b) u‖) :
    z ≠ 0 ∧ deriv (fun w => residueDeformationEquation m u s ((t, b), w)) z ≠ 0 := by
  have hnum : (m 0 : ℂ) * MvPolynomial.eval (Fin.cons (t * z) b) u -
      (t * z) * MvPolynomial.eval (Fin.cons (t * z) b) (MvPolynomial.pderiv 0 u) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    simp only [norm_mul, Complex.norm_natCast] at hn
    simp only [norm_mul] at hbound
    exact (ne_of_lt hbound) hn.symm
  exact mul_ne_zero_iff.mp ((residueDeformationEquation_logderiv m u s t z b hroot) ▸ hnum)

end
end DuistermaatVanDerKallen
