import DuistermaatVanDerKallen.AnalyticTransport
import Mathlib.Analysis.Analytic.Within

/-! Analytic dependence of the actual complete Laurent segment transport,
including varying velocity, initial point, and time. The admissible parameter
set carries exactly the existing good-segment hypothesis. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- Initial points and velocities for which the manuscript's segment-exclusion
hypothesis guarantees complete transport. -/
def admissibleSegmentParameters {d : ℕ} (f : MultiLaurent d) : Set (ℂ × (Fin d → ℂ)) :=
  {p | (∀ i, p.2 i ≠ 0) ∧ GoodSegment f (laurentEval f p.2) p.1}

/-- Existing chosen complete transport, expressed on ambient parameters. Values
outside the admissible set are only a totalization and have no transport claim. -/
def laurentSegmentCurve {d : ℕ} (f : MultiLaurent d)
    (p : ℂ × (Fin d → ℂ)) : ℝ → Fin d → ℂ := by
  classical
  exact if hp : p ∈ admissibleSegmentParameters f then
    fiberCurve hp.2 ⟨p.2, hp.1, rfl⟩
  else fun _ => p.2

/-- The initial-value identity also holds for the harmless totalization. -/
theorem laurentSegmentCurve_zero {d : ℕ} (f : MultiLaurent d)
    (p : ℂ × (Fin d → ℂ)) : laurentSegmentCurve f p 0 = p.2 := by
  unfold laurentSegmentCurve
  split_ifs with hp
  · exact (fiberCurve_spec hp.2 ⟨p.2, hp.1, rfl⟩).1
  · rfl

theorem laurentSegmentCurve_spec {d : ℕ} (f : MultiLaurent d)
    {p : ℂ × (Fin d → ℂ)} (hp : p ∈ admissibleSegmentParameters f) :
    ∀ t ∈ Icc (0 : ℝ) 1, laurentSegmentCurve f p t ∈ laurentRegularDomain f ∧
      HasDerivAt (laurentSegmentCurve f p)
        (laurentVectorField f p.1 (laurentSegmentCurve f p t)) t := by
  rw [laurentSegmentCurve, dite_eq_left hp]
  intro t ht
  exact ⟨((fiberCurve_spec hp.2 ⟨p.2, hp.1, rfl⟩).2 t ht).1,
    ((fiberCurve_spec hp.2 ⟨p.2, hp.1, rfl⟩).2 t ht).2.1⟩

/-- Analytic dependence of complete chosen transport jointly in velocity,
initial point and time, within precisely the admissible parameter set. -/
theorem laurentSegmentCurve_joint_analytic {d : ℕ} (f : MultiLaurent d) :
    ContDiffOn ℝ ⊤ (fun q : (ℂ × (Fin d → ℂ)) × ℝ => laurentSegmentCurve f q.1 q.2)
      (admissibleSegmentParameters f ×ˢ Icc (0 : ℝ) 1) := by
  intro q hq
  exact laurent_family_joint_analytic f hq.1 contDiffWithinAt_fst
    (fun p hp => laurentSegmentCurve_spec f hp)
    (by simpa only [laurentSegmentCurve_zero] using
      (contDiffWithinAt_snd : ContDiffWithinAt ℝ ⊤ Prod.snd (admissibleSegmentParameters f) q.1)) hq.2

/-- Endpoint dependence on velocity and initial point. -/
theorem laurentSegmentCurve_endpoint_analytic {d : ℕ} (f : MultiLaurent d) :
    ContDiffOn ℝ ⊤ (fun p => laurentSegmentCurve f p 1) (admissibleSegmentParameters f) := by
  intro p hp
  exact laurent_family_analytic f hp contDiffWithinAt_fst
    (fun q hq => laurentSegmentCurve_spec f hq)
    (by simpa only [laurentSegmentCurve_zero] using
      (contDiffWithinAt_snd : ContDiffWithinAt ℝ ⊤ Prod.snd (admissibleSegmentParameters f) p))
    1 (by simp)

/-- The ambient-parameter choice agrees with the original fiber choice on
its entire unit trajectory, by uniqueness. -/
theorem laurentSegmentCurve_eq_fiberCurve {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) :
    EqOn (laurentSegmentCurve f (a, z.val)) (fiberCurve h z) (Icc (0 : ℝ) 1) := by
  have hp : (a, z.val) ∈ admissibleSegmentParameters f := by
    refine ⟨z.property.1, ?_⟩
    simpa only [z.property.2] using h
  exact laurent_segment_unique f a (laurentSegmentCurve_spec f hp)
    (fun t ht => ⟨((fiberCurve_spec h z).2 t ht).1, ((fiberCurve_spec h z).2 t ht).2.1⟩)
    ((laurentSegmentCurve_zero f (a, z.val)).trans (fiberCurve_spec h z).1.symm)

/-- Fiber transport has a real analytic ambient extension near each initial
fiber point. This states the local extension precisely, without presupposing
manifold instances on the fibers. -/
theorem fiberTransport_has_analytic_extension {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) :
    ∃ G : (Fin d → ℂ) → (Fin d → ℂ), AnalyticAt ℝ G z.val ∧
      ∀ᶠ y in 𝓝[{y | (∀ i, y i ≠ 0) ∧ laurentEval f y = s}] z.val,
        ∀ hy : (∀ i, y i ≠ 0) ∧ laurentEval f y = s,
          G y = (fiberTransport h ⟨y, hy⟩).val := by
  let S : Set (Fin d → ℂ) := {y | (∀ i, y i ≠ 0) ∧ laurentEval f y = s}
  have hmap : MapsTo (fun y => (a, y)) S (admissibleSegmentParameters f) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    simpa only [hy.2] using h
  have hc : ContDiffWithinAt ℝ ⊤ (fun y => laurentSegmentCurve f (a, y) 1) S z.val :=
    (laurentSegmentCurve_endpoint_analytic f (a, z.val) (hmap z.property)).comp z.val
      (contDiffWithinAt_const.prodMk contDiffWithinAt_id) hmap
  obtain ⟨G, heq, hG⟩ := analyticWithinAt_iff_exists_analyticAt.mp hc.analyticWithinAt
  refine ⟨G, hG, ?_⟩
  have heq' : (fun y => laurentSegmentCurve f (a, y) 1) =ᶠ[𝓝[S] z.val] G :=
    heq.filter_mono (nhdsWithin_mono _ (subset_insert _ _))
  filter_upwards [heq'] with y hy
  intro hys
  exact hy.symm.trans (laurentSegmentCurve_eq_fiberCurve h ⟨y, hys⟩ (by simp))

/-- The inverse fiber transport has the same local analytic extension property. -/
theorem fiberTransportBack_has_analytic_extension {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f (s + a)) :
    ∃ G : (Fin d → ℂ) → (Fin d → ℂ), AnalyticAt ℝ G z.val ∧
      ∀ᶠ y in 𝓝[{y | (∀ i, y i ≠ 0) ∧ laurentEval f y = s + a}] z.val,
        ∀ hy : (∀ i, y i ≠ 0) ∧ laurentEval f y = s + a,
          G y = (fiberTransportBack h ⟨y, hy⟩).val := by
  simpa only [fiberTransportBack, fiberTransport] using
    fiberTransport_has_analytic_extension h.reverse z

/-- Joint transport admits an analytic ambient germ at every admissible
velocity/initial-point/time triple, including time zero and time one. -/
theorem laurentSegmentCurve_has_analytic_extension {d : ℕ} (f : MultiLaurent d)
    {p : ℂ × (Fin d → ℂ)} (hp : p ∈ admissibleSegmentParameters f)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ G : ((ℂ × (Fin d → ℂ)) × ℝ) → Fin d → ℂ, AnalyticAt ℝ G (p, t) ∧
      (fun q => laurentSegmentCurve f q.1 q.2) =ᶠ[
        𝓝[admissibleSegmentParameters f ×ˢ Icc (0 : ℝ) 1] (p, t)] G := by
  obtain ⟨G, heq, hG⟩ := analyticWithinAt_iff_exists_analyticAt.mp
    ((laurentSegmentCurve_joint_analytic f (p, t) ⟨hp, ht⟩).analyticWithinAt)
  exact ⟨G, hG, heq.filter_mono (nhdsWithin_mono _ (subset_insert _ _))⟩

end

end DuistermaatVanDerKallen
