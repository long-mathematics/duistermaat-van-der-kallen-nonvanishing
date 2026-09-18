import DuistermaatVanDerKallen.FaceReduction
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Transvection.Basic

/-! Explicit integral coordinates adapted to finite support. The first coordinate
is a weight `(1, N, ..., N^(d-1))` separating the support. Integer shears then
make its unique minimum the strict minimum in every coordinate. This replaces
the manuscript's rational-density and primitive-vector extension step. -/

open Filter
noncomputable section
namespace DuistermaatVanDerKallen

def exponentPolynomial {d : ℕ} (a : Fin d → ℤ) : Polynomial ℤ :=
  ∑ i, Polynomial.monomial i.val (a i)

theorem exponentPolynomial_coeff {d : ℕ} (a : Fin d → ℤ) (i : Fin d) :
    (exponentPolynomial a).coeff i.val = a i := by
  classical
  simp only [exponentPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Fin.val_ne_of_ne hji]
  · simp

theorem exponentPolynomial_injective {d : ℕ} :
    Function.Injective (exponentPolynomial (d := d)) := by
  intro a b h
  funext i
  have hi := congrArg (fun p : Polynomial ℤ => p.coeff i.val) h
  simpa only [exponentPolynomial_coeff] using hi

theorem exists_integer_weight_injOn {d : ℕ} (S : Finset (Fin d → ℤ)) :
    ∃ N : ℤ, Set.InjOn (fun a : Fin d → ℤ => ∑ i, a i * N ^ i.val) S := by
  have he : ∀ᶠ N : ℤ in cofinite, ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → (exponentPolynomial a).eval N ≠ (exponentPolynomial b).eval N := by
    apply S.eventually_all.mpr
    intro a _
    apply S.eventually_all.mpr
    intro b _
    by_cases hab : a = b
    · exact Eventually.of_forall (by simp [hab])
    · have hp : exponentPolynomial a - exponentPolynomial b ≠ 0 :=
        sub_ne_zero.mpr (fun h => hab (exponentPolynomial_injective h))
      filter_upwards [Polynomial.eventually_eval_ne_zero_cofinite hp] with N hN
      simpa only [Polynomial.eval_sub, sub_ne_zero] using fun _ : a ≠ b => hN
  obtain ⟨N, hN⟩ := he.exists
  refine ⟨N, ?_⟩
  intro a ha b hb hab
  by_contra hne
  apply hN a ha b hb hne
  simpa [exponentPolynomial, Polynomial.eval_finsetSum] using hab

def weightLinearForm {R : Type*} [CommRing R] {d : ℕ} (w : Fin d → R) :
    (Fin d → R) →ₗ[R] R :=
  ∑ i, w i • LinearMap.proj i

theorem weightLinearForm_apply {R : Type*} [CommRing R] {d : ℕ}
    (w x : Fin d → R) : weightLinearForm w x = ∑ i, w i * x i := by
  simp [weightLinearForm]

def firstCoordinateShear {R : Type*} [CommRing R] {d : ℕ}
    (w : Fin (d + 1) → R) (hw : w 0 = 1) :
    (Fin (d + 1) → R) ≃ₗ[R] (Fin (d + 1) → R) :=
  LinearEquiv.transvection (f := weightLinearForm w - LinearMap.proj 0)
    (v := Pi.single 0 1) (by
      simp [weightLinearForm_apply, Pi.single_apply, hw])

theorem firstCoordinateShear_zero {R : Type*} [CommRing R] {d : ℕ}
    (w : Fin (d + 1) → R) (hw : w 0 = 1) (x : Fin (d + 1) → R) :
    firstCoordinateShear w hw x 0 = ∑ i, w i * x i := by
  simp [firstCoordinateShear, LinearMap.transvection.apply, weightLinearForm_apply]

theorem firstCoordinateShear_other {R : Type*} [CommRing R] {d : ℕ}
    (w : Fin (d + 1) → R) (hw : w 0 = 1) (x : Fin (d + 1) → R)
    (i : Fin (d + 1)) (hi : i ≠ 0) : firstCoordinateShear w hw x i = x i := by
  simp [firstCoordinateShear, LinearMap.transvection.apply, hi]

/-- A unimodular first coordinate has a unique minimum on every finite nonempty set. -/
theorem exists_first_coordinate_minimum {d : ℕ} (S : Finset (Fin (d + 1) → ℤ))
    (hS : S.Nonempty) :
    ∃ E : (Fin (d + 1) → ℤ) ≃ₗ[ℤ] (Fin (d + 1) → ℤ),
      ∃ v ∈ S, ∀ a ∈ S, a ≠ v → E v 0 < E a 0 := by
  obtain ⟨N, hN⟩ := exists_integer_weight_injOn S
  let w : Fin (d + 1) → ℤ := fun i => N ^ i.val
  have hw : w 0 = 1 := by simp [w]
  let E := firstCoordinateShear w hw
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun a => E a 0) hS
  refine ⟨E, v, hv, ?_⟩
  intro a ha hav
  apply lt_of_le_of_ne (hmin a ha)
  intro he
  apply hav
  apply hN ha hv
  have he' : (∑ i, w i * v i) = ∑ i, w i * a i := by
    simpa only [E, firstCoordinateShear_zero] using he
  simpa only [w, mul_comm] using he'.symm

/-- Integer shears place the same support point strictly below every other
support point in every coordinate. -/
theorem exists_all_coordinate_minimum {d : ℕ} (S : Finset (Fin (d + 1) → ℤ))
    (hS : S.Nonempty) :
    ∃ E : (Fin (d + 1) → ℤ) ≃ₗ[ℤ] (Fin (d + 1) → ℤ),
      ∃ v ∈ S, ∀ a ∈ S, a ≠ v → ∀ i, E v i < E a i := by
  obtain ⟨E, v, hv, hmin⟩ := exists_first_coordinate_minimum S hS
  have hb : ∀ᶠ M : ℤ in atTop, 0 ≤ M ∧ ∀ a ∈ S, ∀ i,
      -(E a i - E v i) < M := by
    apply (eventually_ge_atTop 0).and
    apply S.eventually_all.mpr
    intro a _
    exact eventually_all.mpr (fun i => eventually_gt_atTop _)
  obtain ⟨M, hM, hbound⟩ := hb.exists
  let c : Fin (d + 1) → ℤ := fun i => if i = 0 then 0 else M
  let T : (Fin (d + 1) → ℤ) ≃ₗ[ℤ] (Fin (d + 1) → ℤ) :=
    LinearEquiv.transvection (f := LinearMap.proj 0) (v := c) (by simp [c])
  refine ⟨E.trans T, v, hv, ?_⟩
  intro a ha hav i
  have hd : 1 ≤ E a 0 - E v 0 := by have := hmin a ha hav; omega
  have ht (x : Fin (d + 1) → ℤ) : T x i = x i + x 0 * c i := by
    simp [T, LinearMap.transvection.apply]
  change T (E v) i < T (E a) i
  rw [ht, ht]
  by_cases hi : i = 0
  · simpa [c, hi] using hmin a ha hav
  · simp only [c, hi, ite_false]
    have hm := hbound a ha i
    nlinarith [mul_nonneg hM (sub_nonneg.mpr hd)]

end DuistermaatVanDerKallen
