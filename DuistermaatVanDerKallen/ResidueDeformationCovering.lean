import DuistermaatVanDerKallen.ResidueDeformationBounds
import DuistermaatVanDerKallen.RootCounting

/-! Covering transport preserves the number of roots through the deformation
of the polynomial unit. The base circle coordinates are fixed during transport. -/

namespace DuistermaatVanDerKallen
noncomputable section

def residueDeformationSlice {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s : ℂ) (b : Fin d → ℂ) (q : ℂ × ℂ) : ℂ :=
  residueDeformationEquation m u s ((q.1, b), q.2)

theorem residueDeformationSlice_contDiff {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (s : ℂ) (b : Fin d → ℂ) :
    ContDiff ℂ ⊤ (residueDeformationSlice m u s b) :=
  (residueDeformationEquation_contDiff m u s).comp (by fun_prop)

def residueDeformationDisc : Set ℂ := Metric.closedBall 0 1

def residueDeformationZero : residueDeformationDisc := ⟨0, by simp [residueDeformationDisc]⟩
def residueDeformationOne : residueDeformationDisc := ⟨1, by simp [residueDeformationDisc]⟩

def residueDeformationPath : Path residueDeformationZero residueDeformationOne where
  toFun t := ⟨((t : ℝ) : ℂ), by
    simp only [residueDeformationDisc, Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact t.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_ofReal.comp continuous_subtype_val
  source' := by ext; simp [residueDeformationZero]
  target' := by ext; simp [residueDeformationOne]

namespace ResidueDiscData
variable {d : ℕ} {m : Fin (d + 1) →₀ ℕ} {u : MvPolynomial (Fin (d + 1)) ℂ}
variable (D : ResidueDiscData m u)

theorem deformationSlice_partial_isInvertible {s : ℂ} (hs : D.threshold < ‖s‖)
    {b : Fin d → ℂ} (hb : ∀ i, ‖b i‖ = D.radius)
    (q : CompactRootSpace (residueDeformationSlice m u s b) residueDeformationDisc D.radius) :
    (fderiv ℂ (residueDeformationSlice m u s b) q.val ∘L .inr ℂ ℂ ℂ).IsInvertible := by
  apply complexLinearMap_isInvertible
  have ht : ‖q.val.1‖ ≤ 1 := by
    simpa [residueDeformationDisc, Metric.mem_closedBall, dist_zero_right] using q.property.1
  have hreg := D.deformation_regular_root hs ht q.property.2.1 hb q.property.2.2
  have hd := (((residueDeformationSlice_contDiff m u s b).differentiable (by simp)).differentiableAt
    (x := q.val)).hasFDerivAt
  have hg : HasDerivAt (fun z : ℂ => (q.val.1, z)) (0, 1) q.val.2 :=
    (hasDerivAt_const q.val.2 q.val.1).prodMk (hasDerivAt_id q.val.2)
  have he := (hd.comp_hasDerivAt q.val.2 hg).deriv
  change fderiv ℂ (residueDeformationSlice m u s b) q.val (0, 1) ≠ 0
  rw [← he]
  exact hreg.2.2

theorem isCoveringMap_deformationProjection {s : ℂ} (hs : D.threshold < ‖s‖)
    {b : Fin d → ℂ} (hb : ∀ i, ‖b i‖ = D.radius) :
    IsCoveringMap (compactRootProjection (residueDeformationSlice m u s b)
      residueDeformationDisc D.radius) := by
  apply isCoveringMap_compactRootProjection
    (hB := isCompact_closedBall (0 : ℂ) 1)
    (hP := (residueDeformationSlice_contDiff m u s b).continuous)
  intro q
  have ht : ‖q.val.1‖ ≤ 1 := by
    simpa [residueDeformationDisc, Metric.mem_closedBall, dist_zero_right] using q.property.1
  exact ⟨(D.deformation_regular_root hs ht q.property.2.1 hb q.property.2.2).2.1,
    (residueDeformationSlice_contDiff m u s b).contDiffAt.of_le (by simp),
    D.deformationSlice_partial_isInvertible hs hb q⟩

theorem deformation_fiber_card_eq {s : ℂ} (hs : D.threshold < ‖s‖)
    {b : Fin d → ℂ} (hb : ∀ i, ‖b i‖ = D.radius) :
    Nat.card (compactRootProjection (residueDeformationSlice m u s b)
      residueDeformationDisc D.radius ⁻¹' {residueDeformationZero}) =
    Nat.card (compactRootProjection (residueDeformationSlice m u s b)
      residueDeformationDisc D.radius ⁻¹' {residueDeformationOne}) :=
  covering_fiber_card_eq_along_path (D.isCoveringMap_deformationProjection hs hb) residueDeformationPath

end ResidueDiscData
end
end DuistermaatVanDerKallen
