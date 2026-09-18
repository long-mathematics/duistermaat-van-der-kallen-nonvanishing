import DuistermaatVanDerKallen.LaurentGeometry
import DuistermaatVanDerKallen.FiberTransport
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Analytic local product coordinates at regular Laurent points. The first
coordinate is the original Laurent evaluation; the second lies in the kernel
of its actual real differential. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- The actual real differential in the original torus coordinates. -/
def laurentRealDifferential {d : ℕ} (f : MultiLaurent d) (z : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℝ] ℂ :=
  (coordinateDifferential (polynomialTorusGradient (laurentRepresentative f) z)).restrictScalars ℝ

theorem laurentEval_hasRealFDerivAt {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    HasFDerivAt (laurentEval f) (laurentRealDifferential f z) z :=
  (laurentEval_hasFDerivAt f hz).restrictScalars ℝ

/-- The already proved scalar lift supplies surjectivity of this differential. -/
theorem laurentRealDifferential_surjective {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    Function.Surjective (laurentRealDifferential f z) := by
  intro a
  refine ⟨laurentVectorField f a z, ?_⟩
  have he := laurentVectorField_derivative f a hz
  rw [(laurentEval_hasFDerivAt f hz.1).fderiv] at he
  exact he

/-- The complemented-kernel data for the regular-level implicit function theorem. -/
def laurentImplicitData {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ImplicitFunctionData ℝ (Fin d → ℂ) ℂ (laurentRealDifferential f z).ker :=
  ((laurentEval_contDiffAt f hz.1).hasStrictFDerivAt'
    (laurentEval_hasRealFDerivAt f hz.1) (by simp)).implicitFunctionDataOfComplemented
      (laurentEval f) (laurentRealDifferential f z)
      (LinearMap.range_eq_top.mpr (laurentRealDifferential_surjective f hz))
      (laurentRealDifferential f z).ker_closedComplemented_of_finiteDimensional_range

/-- The local product chart has the Laurent evaluation as its first coordinate. -/
theorem laurentImplicitData_fst {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) (y : Fin d → ℂ) :
    ((laurentImplicitData f hz).toOpenPartialHomeomorph y).1 = laurentEval f y := rfl

/-- Its forward map is analytic at every point of the regular torus domain. -/
theorem laurentImplicitData_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f)
    {y : Fin d → ℂ} (hy : y ∈ laurentRegularDomain f) :
    ContDiffAt ℝ ⊤ (laurentImplicitData f hz).toOpenPartialHomeomorph y := by
  let π := Classical.choose
    (laurentRealDifferential f z).ker_closedComplemented_of_finiteDimensional_range
  change ContDiffAt ℝ ⊤ (fun x => (laurentEval f x, π (x - z))) y
  exact (laurentEval_contDiffAt f hy.1).prodMk
    (π.contDiff.contDiffAt.comp y (contDiffAt_id.sub contDiffAt_const))

/-- The inverse product chart is analytic near the reference point. -/
theorem laurentImplicitData_symm_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ContDiffAt ℝ ⊤ (laurentImplicitData f hz).toOpenPartialHomeomorph.symm
      ((laurentImplicitData f hz).toOpenPartialHomeomorph z) := by
  have hl : ContDiffAt ℝ ⊤ (laurentImplicitData f hz).leftFun (laurentImplicitData f hz).pt :=
    laurentEval_contDiffAt f hz.1
  let π := Classical.choose
    (laurentRealDifferential f z).ker_closedComplemented_of_finiteDimensional_range
  have hr : ContDiffAt ℝ ⊤ (laurentImplicitData f hz).rightFun (laurentImplicitData f hz).pt :=
    π.contDiff.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const)
  exact ImplicitFunctionData.contDiffAt_implicitFunction hl hr (by simp)

/-- At each regular point there are analytic product coordinates, with analytic
inverse, whose first coordinate is the original Laurent polynomial. Their
source is entirely inside the regular torus. -/
theorem laurent_regular_product_chart {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ℂ × (laurentRealDifferential f z).ker),
      z ∈ e.source ∧ e.source ⊆ laurentRegularDomain f ∧
      (∀ y, (e y).1 = laurentEval f y) ∧
      ContDiffOn ℝ ⊤ e e.source ∧ ContDiffOn ℝ ⊤ e.symm e.target := by
  let e := (laurentImplicitData f hz).toOpenPartialHomeomorph
  let V := {q | ContDiffAt ℝ ⊤ e.symm q}
  have hV : IsOpen V := isOpen_iff_mem_nhds.mpr (fun q hq =>
    (show ContDiffAt ℝ ⊤ e.symm q from hq).eventually (by simp))
  have hVz : e z ∈ V := laurentImplicitData_symm_contDiffAt f hz
  have hez : z ∈ e.source := (laurentImplicitData f hz).pt_mem_toOpenPartialHomeomorph_source
  let e₀ := (e.symm.restrOpen V hV).symm
  let e₁ := e₀.restrOpen (laurentRegularDomain f) (laurentRegularDomain_isOpen f)
  have hsource : e₁.source = {y | (y ∈ e.source ∧ e y ∈ V) ∧ y ∈ laurentRegularDomain f} := rfl
  have htarget : e₁.target = {q | (q ∈ e.target ∧ q ∈ V) ∧ e.symm q ∈ laurentRegularDomain f} := rfl
  refine ⟨e₁, ⟨⟨hez, hVz⟩, hz⟩, fun y hy => hy.2,
    fun y => laurentImplicitData_fst f hz y, ?_, ?_⟩
  · intro y hy
    exact (laurentImplicitData_contDiffAt f hz hy.2).contDiffWithinAt
  · intro q hq
    exact (show ContDiffAt ℝ ⊤ e.symm q from hq.1.2).contDiffWithinAt

/-- The tangent kernel of a regular fiber has real dimension `2d - 2`. -/
theorem laurentRealDifferential_ker_finrank {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    Module.finrank ℝ (laurentRealDifferential f z).ker = 2 * d - 2 := by
  have h := (laurentRealDifferential f z).toLinearMap.finrank_range_add_finrank_ker
  have hr : (laurentRealDifferential f z).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr (laurentRealDifferential_surjective f hz)
  rw [hr] at h
  simp only [finrank_top, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-- One fixed Euclidean model for every regular fiber in rank `d`. -/
abbrev LaurentFiberModel (d : ℕ) := Fin (2 * d - 2) → ℝ

/-- The local tangent kernel is continuously linearly equivalent to the fixed
real model; existence of a regular point handles the low-rank edge cases. -/
def laurentKernelEquiv {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    (laurentRealDifferential f z).ker ≃L[ℝ] LaurentFiberModel d :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [laurentRealDifferential_ker_finrank f hz, Module.finrank_fin_fun])

/-- Regular product coordinates can be chosen in a model independent of the
reference point, as required for a fiber atlas. -/
theorem laurent_regular_product_chart_fixed {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (ℂ × LaurentFiberModel d),
      z ∈ e.source ∧ e.source ⊆ laurentRegularDomain f ∧
      (∀ y, (e y).1 = laurentEval f y) ∧
      ContDiffOn ℝ ⊤ e e.source ∧ ContDiffOn ℝ ⊤ e.symm e.target := by
  obtain ⟨e, hez, hreg, hfst, he, hei⟩ := laurent_regular_product_chart f hz
  let L := (ContinuousLinearEquiv.refl ℝ ℂ).prodCongr (laurentKernelEquiv f hz)
  let e' := e.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hs : e'.source = e.source := by simp [e']
  refine ⟨e', by simpa only [hs] using hez, by simpa only [hs] using hreg,
    fun y => hfst y, ?_, ?_⟩
  · change ContDiffOn ℝ ⊤ (L ∘ e) e'.source
    rw [hs]
    exact L.contDiff.comp_contDiffOn he
  · exact hei.comp L.symm.contDiff.contDiffOn (fun q hq => hq.2)

end

end DuistermaatVanDerKallen
