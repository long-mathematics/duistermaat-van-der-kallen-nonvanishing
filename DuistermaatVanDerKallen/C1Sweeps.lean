import DuistermaatVanDerKallen.DrivenContinuity
import DuistermaatVanDerKallen.PiecewiseTransport

/-! Compact sweeps of the complete C¹ transport and finite chains of pieces. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section
namespace LaurentC1Path
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

/-- The actual chosen trajectory depends jointly on the initial point and time. -/
theorem ambientCurve_joint_continuous (h : LaurentC1Path f s t) :
    ContinuousOn (fun q : (Fin d → ℂ) × ℝ => h.ambientCurve q.1 q.2)
      ({z | (∀ i, z i ≠ 0) ∧ laurentEval f z = s} ×ˢ Icc (0 : ℝ) 1) := by
  intro q hq
  apply laurent_driven_family_joint_continuous_on f h.velocity h.velocity_continuous hq.1 _ _ hq.2
  · intro y hy r hr
    rw [h.ambientCurve_eq ⟨y, hy⟩]
    exact ⟨((h.curve_spec ⟨y, hy⟩).2 r hr).1, ((h.curve_spec ⟨y, hy⟩).2 r hr).2.1⟩
  · simp only [ambientCurve_zero]
    exact contDiffWithinAt_id

/-- Joint continuity with the fiber and closed time interval as subtypes. -/
theorem curves_continuous (h : LaurentC1Path f s t) :
    Continuous (fun p : LaurentFiber f s × CurveTime => h.curve p.1 p.2) := by
  have hc := h.ambientCurve_joint_continuous.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
    (fun p : LaurentFiber f s × CurveTime => ⟨p.1.property, p.2.property⟩)
  simpa only [Function.comp_def, ambientCurve_eq] using hc

/-- The swept support in the actual coordinate torus. -/
def sweep (h : LaurentC1Path f s t) (C : Set (LaurentFiber f s)) : Set (Fin d → ℂ) :=
  (fun p : LaurentFiber f s × CurveTime => h.curve p.1 p.2) '' (C ×ˢ univ)

theorem sweep_isCompact (h : LaurentC1Path f s t) (C : Set (LaurentFiber f s)) (hC : IsCompact C) :
    IsCompact (h.sweep C) :=
  (hC.prod isCompact_univ).image h.curves_continuous

/-- Both coordinate escape and approach to the critical locus are excluded
throughout the sweep. Compactness alone is not substituted for regularity. -/
theorem sweep_subset_regular (h : LaurentC1Path f s t) (C : Set (LaurentFiber f s)) :
    h.sweep C ⊆ laurentRegularDomain f := by
  rintro _ ⟨⟨z, r⟩, _, rfl⟩
  exact ((h.curve_spec z).2 r r.property).1

/-- Every transported base value is exactly on the prescribed path. -/
theorem sweep_base (h : LaurentC1Path f s t) (C : Set (LaurentFiber f s)) :
    MapsTo (laurentEval f) (h.sweep C) (h.base '' Icc (0 : ℝ) 1) := by
  rintro _ ⟨⟨z, r⟩, _, rfl⟩
  exact ⟨r, r.property, ((h.curve_spec z).2 r r.property).2.2.symm⟩

end LaurentC1Path
namespace LaurentC1Chain
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

theorem transport_continuous (h : LaurentC1Chain f s t) : Continuous h.transport := by
  induction h with
  | single h => simpa only [transport] using h.transport_continuous
  | append h k ih => simpa only [transport] using k.transport_continuous.comp ih

theorem transportBack_continuous (h : LaurentC1Chain f s t) : Continuous h.transportBack := by
  induction h with
  | single h => simpa only [transportBack] using h.reverse.transport_continuous
  | append h k ih => simpa only [transportBack] using ih.comp k.reverse.transport_continuous

/-- The swept support of a finite chain is the union of successive piece
sweeps, with each piece starting from the preceding endpoint image. -/
def sweep : {s t : ℂ} → (h : LaurentC1Chain f s t) → Set (LaurentFiber f s) → Set (Fin d → ℂ)
  | _, _, .single h, C => h.sweep C
  | _, _, .append h k, C => h.sweep C ∪ k.sweep (h.transport '' C)

theorem sweep_isCompact (h : LaurentC1Chain f s t) (C : Set (LaurentFiber f s)) (hC : IsCompact C) :
    IsCompact (h.sweep C) := by
  induction h with
  | single h => simpa only [sweep] using h.sweep_isCompact C hC
  | append h k ih =>
    simpa only [sweep] using ih.union (k.sweep_isCompact _ (hC.image h.transport_continuous))

theorem sweep_subset_regular (h : LaurentC1Chain f s t) (C : Set (LaurentFiber f s)) :
    h.sweep C ⊆ laurentRegularDomain f := by
  induction h with
  | single h => simpa only [sweep] using h.sweep_subset_regular C
  | append h k ih =>
    simpa only [sweep] using union_subset ih (k.sweep_subset_regular (h.transport '' C))

end LaurentC1Chain
end
end DuistermaatVanDerKallen
