import DuistermaatVanDerKallen.FiberAtlas
import DuistermaatVanDerKallen.SegmentAnalytic
import DuistermaatVanDerKallen.FiberContinuity
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The actual complete segment maps as analytic manifold diffeomorphisms. -/

open Set Filter
open scoped Topology Manifold

namespace DuistermaatVanDerKallen

noncomputable section

/-- Local analytic ambient extensions induce analytic maps between the regular
fiber manifolds constructed from their level-set charts. -/
theorem regularFiber_map_contMDiff_of_extensions {d : ℕ} (f : MultiLaurent d) (s t : ℂ)
    [Fact (RegularLaurentValue f s)] [Fact (RegularLaurentValue f t)]
    (g : LaurentFiber f s → LaurentFiber f t) (hg : Continuous g)
    (hext : ∀ x : LaurentFiber f s, ∃ G : (Fin d → ℂ) → (Fin d → ℂ),
      AnalyticAt ℝ G x.val ∧ ∀ᶠ y in 𝓝 x, (g y).val = G y.val) :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ g := by
  intro x
  obtain ⟨G, hG, heq⟩ := hext x
  have hambient : ContMDiffAt (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (Fin d → ℂ)) ⊤ (fun y => (g y).val) x :=
    (hG.contDiffAt.contMDiffAt.comp x (regularFiber_val_contMDiff f s x)).congr_of_eventuallyEq heq
  apply contMDiffAt_iff_target.mpr
  refine ⟨hg.continuousAt, ?_⟩
  have hchart : ContDiffAt ℝ ⊤ (fun y => (regularFiberProductChart f t (g x) y).2) (g x).val :=
    ((regularFiberProductChart_spec f t (g x)).2.2.2.1.contDiffAt
      ((regularFiberProductChart f t (g x)).open_source.mem_nhds
        (regularFiberProductChart_spec f t (g x)).1)).snd
  have hh := hchart.contMDiffAt.comp x hambient
  simpa only [extChartAt, OpenPartialHomeomorph.extend, mfld_simps, chartAt_regularFiber,
    regularFiberChart, fiberSliceChart_apply, Function.comp_def] using hh

/-- Analyticity of the actual forward transport as a map of regular fibers. -/
theorem fiberTransport_contMDiff {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    [Fact (RegularLaurentValue f s)] [Fact (RegularLaurentValue f (s + a))]
    (h : GoodSegment f s a) :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ (fiberTransport h) := by
  apply regularFiber_map_contMDiff_of_extensions f s (s + a) (fiberTransport h)
    (fiberTransport_continuous h)
  intro x
  obtain ⟨G, hG, heq⟩ := fiberTransport_has_analytic_extension h x
  refine ⟨G, hG, ?_⟩
  have hv : Tendsto (Subtype.val : LaurentFiber f s → Fin d → ℂ) (𝓝 x)
      (𝓝[{y | (∀ i, y i ≠ 0) ∧ laurentEval f y = s}] x.val) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.continuousAt,
      Filter.Eventually.of_forall (fun y => y.property)⟩
  filter_upwards [hv.eventually heq] with y hy
  exact (hy y.property).symm

/-- Analyticity of the actual inverse transport as a map of regular fibers. -/
theorem fiberTransportBack_contMDiff {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    [Fact (RegularLaurentValue f s)] [Fact (RegularLaurentValue f (s + a))]
    (h : GoodSegment f s a) :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ (fiberTransportBack h) := by
  apply regularFiber_map_contMDiff_of_extensions f (s + a) s (fiberTransportBack h)
    (fiberTransportBack_continuous h)
  intro x
  obtain ⟨G, hG, heq⟩ := fiberTransportBack_has_analytic_extension h x
  refine ⟨G, hG, ?_⟩
  have hv : Tendsto (Subtype.val : LaurentFiber f (s + a) → Fin d → ℂ) (𝓝 x)
      (𝓝[{y | (∀ i, y i ≠ 0) ∧ laurentEval f y = s + a}] x.val) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.continuousAt,
      Filter.Eventually.of_forall (fun y => y.property)⟩
  filter_upwards [hv.eventually heq] with y hy
  exact (hy y.property).symm

/-- Complete segment transport is an analytic diffeomorphism. The regular-fiber
instances are derived from the segment hypothesis in the definition itself. -/
def fiberTransportDiffeomorph {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) :
    letI : Fact (RegularLaurentValue f s) := ⟨h.regularValue⟩
    letI : Fact (RegularLaurentValue f (s + a)) := ⟨h.reverse.regularValue⟩
    Diffeomorph (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) (LaurentFiber f s) (LaurentFiber f (s + a)) ⊤ := by
  letI : Fact (RegularLaurentValue f s) := ⟨h.regularValue⟩
  letI : Fact (RegularLaurentValue f (s + a)) := ⟨h.reverse.regularValue⟩
  exact { toEquiv := fiberTransportEquiv h
          contMDiff_toFun := fiberTransport_contMDiff h
          contMDiff_invFun := fiberTransportBack_contMDiff h }

/-- Manuscript segment transport, assembled with its actual manifold
map, exact base motion, and compact-sweep conclusion for every compact initial
subset (in particular the support of any compact cycle). -/
theorem complete_segment_transport {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) :
    letI : Fact (RegularLaurentValue f s) := ⟨h.regularValue⟩
    letI : Fact (RegularLaurentValue f (s + a)) := ⟨h.reverse.regularValue⟩
    ∃ e : Diffeomorph (modelWithCornersSelf ℝ (LaurentFiberModel d))
        (modelWithCornersSelf ℝ (LaurentFiberModel d))
        (LaurentFiber f s) (LaurentFiber f (s + a)) ⊤,
      e.toEquiv = fiberTransportEquiv h ∧
      (∀ z : LaurentFiber f s, fiberCurve h z 0 = z.val ∧
        ∀ t ∈ Icc (0 : ℝ) 1, fiberCurve h z t ∈ laurentRegularDomain f ∧
          HasDerivAt (fiberCurve h z) (laurentVectorField f a (fiberCurve h z t)) t ∧
          laurentEval f (fiberCurve h z t) = s + t • a) ∧
      ∀ C : Set (LaurentFiber f s), IsCompact C →
        IsCompact ((fun p : LaurentFiber f s × Icc (0 : ℝ) 1 => fiberCurve h p.1 p.2) ''
          (C ×ˢ univ)) ∧
        ((fun p : LaurentFiber f s × Icc (0 : ℝ) 1 => fiberCurve h p.1 p.2) ''
          (C ×ˢ univ)) ⊆ laurentRegularDomain f := by
  let : Fact (RegularLaurentValue f s) := ⟨h.regularValue⟩
  let : Fact (RegularLaurentValue f (s + a)) := ⟨h.reverse.regularValue⟩
  exact ⟨fiberTransportDiffeomorph h, rfl, fiberCurve_spec h,
    fun C hC => ⟨fiberSweep_isCompact h C hC, fiberSweep_subset_regular h C⟩⟩

end

end DuistermaatVanDerKallen
