import DuistermaatVanDerKallen.Targets
import Mathlib.Algebra.MvPolynomial.Basic

/-! A coordinatewise minimum exponent gives a monomial times a polynomial,
with the minimum coefficient as the polynomial's nonzero constant coefficient. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- Nonnegative polynomial exponents included in the Laurent exponent lattice. -/
def natExponent {d : ℕ} : (Fin d →₀ ℕ) →+ (Fin d → ℤ) where
  toFun a i := a i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

theorem natExponent_injective {d : ℕ} : Function.Injective (natExponent (d := d)) := by
  intro a b h
  ext i
  have hi := congrFun h i
  change (a i : ℤ) = (b i : ℤ) at hi
  exact_mod_cast hi

/-- The canonical inclusion of ordinary polynomials into Laurent polynomials. -/
def polynomialLaurentHom {d : ℕ} : MvPolynomial (Fin d) ℂ →+* MultiLaurent d :=
  AddMonoidAlgebra.mapDomainRingHom ℂ natExponent

theorem polynomialLaurentHom_injective {d : ℕ} :
    Function.Injective (polynomialLaurentHom (d := d)) :=
  AddMonoidAlgebra.mapDomain_injective natExponent_injective

theorem polynomialLaurentHom_constantTerm {d : ℕ} (u : MvPolynomial (Fin d) ℂ) :
    constantTerm (polynomialLaurentHom u) = u.coeff 0 := by
  change (Finsupp.mapDomain natExponent u.coeff) 0 = _
  rw [← natExponent.map_zero, Finsupp.mapDomain_apply_of_injective natExponent_injective]

/-- Nonnegative Laurent support is exactly what is needed to come from a polynomial. -/
theorem exists_polynomial_of_nonnegative_support {d : ℕ} (f : MultiLaurent d)
    (hf : ∀ a ∈ f.coeff.support, ∀ i, 0 ≤ a i) :
    ∃ u : MvPolynomial (Fin d) ℂ, polynomialLaurentHom u = f := by
  classical
  refine ⟨AddMonoidAlgebra.comapDomain natExponent natExponent_injective f, ?_⟩
  apply AddMonoidAlgebra.mapDomain_comapDomain
  intro a ha
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).toNat), ?_⟩
  ext i
  change ((Finsupp.equivFunOnFinite.symm (fun i => (a i).toNat)) i : ℤ) = a i
  simpa using Int.toNat_of_nonneg (hf a ha i)

/-- Factoring the coordinatewise minimum exponent retains its exact coefficient. -/
theorem factor_at_coordinate_minimum {d : ℕ} (f : MultiLaurent d) (v : Fin d → ℤ)
    (hmin : ∀ a ∈ f.coeff.support, ∀ i, v i ≤ a i) :
    ∃ u : MvPolynomial (Fin d) ℂ,
      f = AddMonoidAlgebra.single v 1 * polynomialLaurentHom u ∧ u.coeff 0 = f.coeff v := by
  classical
  let q : MultiLaurent d := AddMonoidAlgebra.single (-v) 1 * f
  have hq : ∀ a ∈ q.coeff.support, ∀ i, 0 ≤ a i := by
    intro a ha i
    have hc : f.coeff (v + a) ≠ 0 := by
      simpa [q, AddMonoidAlgebra.coeff_single_mul_apply] using Finsupp.mem_support_iff.mp ha
    have hm := hmin (v + a) (Finsupp.mem_support_iff.mpr hc) i
    simpa using hm
  obtain ⟨u, hu⟩ := exists_polynomial_of_nonnegative_support q hq
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    simp [q, ← mul_assoc, ← AddMonoidAlgebra.one_def]
  · rw [← polynomialLaurentHom_constantTerm, hu]
    simp [q, constantTerm, AddMonoidAlgebra.coeff_single_mul_apply]

end
end DuistermaatVanDerKallen
