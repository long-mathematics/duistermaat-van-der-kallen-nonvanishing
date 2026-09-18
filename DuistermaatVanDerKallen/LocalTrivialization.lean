import DuistermaatVanDerKallen.FiberDiffeomorph
import DuistermaatVanDerKallen.CriticalNeighborhood
import Mathlib.Analysis.Convex.Basic

/-! Smooth local product trivializations constructed from the complete scalar
normalized-gradient transport, with the original Laurent evaluation as base. -/

open Set
open scoped Topology Manifold ContDiff

namespace DuistermaatVanDerKallen
noncomputable section

/-- A base set disjoint from the manuscript's two critical-value sets. -/
def GoodBase {d : ℕ} (f : MultiLaurent d) (D : Set ℂ) : Prop :=
  ∀ s ∈ D, s ∉
    ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f)

theorem GoodBase.segment {d : ℕ} {f : MultiLaurent d} {D : Set ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ D) {s t : ℂ} (hs : s ∈ D) (ht : t ∈ D) :
    GoodSegment f s (t - s) := by
  intro u hu
  apply hD
  have h := hc.lineMap_mem hs ht hu
  simpa only [AffineMap.lineMap_apply_module', add_comm] using h

theorem laurentSegmentCurve_base {d : ℕ} (f : MultiLaurent d)
    {p : ℂ × (Fin d → ℂ)} (hp : p ∈ admissibleSegmentParameters f)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    laurentEval f (laurentSegmentCurve f p t) = laurentEval f p.2 + t • p.1 := by
  rw [laurentSegmentCurve, dite_eq_left hp]
  exact ((fiberCurve_spec hp.2 ⟨p.2, hp.1, rfl⟩).2 t ht).2.2

/-- Reversing the ambient-parameter transport returns its initial point. -/
theorem laurentSegmentCurve_reverse_endpoint {d : ℕ} (f : MultiLaurent d)
    {p : ℂ × (Fin d → ℂ)} (hp : p ∈ admissibleSegmentParameters f) :
    laurentSegmentCurve f (-p.1, laurentSegmentCurve f p 1) 1 = p.2 := by
  have hb := laurentSegmentCurve_base f hp (by simp : (1 : ℝ) ∈ Icc 0 1)
  simp only [one_smul] at hb
  have hr : (-p.1, laurentSegmentCurve f p 1) ∈ admissibleSegmentParameters f := by
    refine ⟨((laurentSegmentCurve_spec f hp 1 (by simp)).1).1, ?_⟩
    change GoodSegment f (laurentEval f (laurentSegmentCurve f p 1)) (-p.1)
    rw [hb]
    exact hp.2.reverse
  have he := laurent_segment_reverse_inverse f p.1 (laurentSegmentCurve_spec f hp)
    (laurentSegmentCurve_spec f hr)
    (laurentSegmentCurve_zero f (-p.1, laurentSegmentCurve f p 1))
  simpa only [sub_self, laurentSegmentCurve_zero] using he (by simp : (1 : ℝ) ∈ Icc 0 1)

/-- Torus points lying over a specified base set. -/
def laurentTube {d : ℕ} (f : MultiLaurent d) (D : Set ℂ) : Set (Fin d → ℂ) :=
  {z | (∀ i, z i ≠ 0) ∧ laurentEval f z ∈ D}

theorem laurentTube_isOpen {d : ℕ} (f : MultiLaurent d) {D : Set ℂ}
    (hD : IsOpen D) : IsOpen (laurentTube f D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hz' : ∀ᶠ y in 𝓝 z, ∀ i, y i ≠ 0 := by
    have ho : IsOpen {y : Fin d → ℂ | ∀ i, y i ≠ 0} := by
      simpa only [ofPred_forall, preimage_ofPred_eq] using
        (isOpen_iInter_of_finite (fun i : Fin d =>
          (isOpen_ne : IsOpen {a : ℂ | a ≠ 0}).preimage (continuous_apply i)))
    exact ho.mem_nhds hz.1
  have he := (laurentEval_contDiffAt f hz.1).continuousAt.preimage_mem_nhds (hD.mem_nhds hz.2)
  exact Filter.inter_mem hz' he

section ConvexTube
variable {d : ℕ} {f : MultiLaurent d} {D : Set ℂ} {b : ℂ}
variable (hD : GoodBase f D) (hc : Convex ℝ D) (hb : b ∈ D)

include hD hc hb in
theorem convexTransport_admissible (s : D) (z : LaurentFiber f b) :
    (s.val - b, z.val) ∈ admissibleSegmentParameters f := by
  refine ⟨z.property.1, ?_⟩
  change GoodSegment f (laurentEval f z.val) (s.val - b)
  rw [z.property.2]
  exact hD.segment hc hb s.property

include hD hc hb in
theorem convexTransportBack_admissible (y : laurentTube f D) :
    (b - laurentEval f y.val, y.val) ∈ admissibleSegmentParameters f :=
  ⟨y.property.1, hD.segment hc y.property.2 hb⟩

/-- Straight transport from the reference fiber across a convex good base. -/
def convexTransport (p : D × LaurentFiber f b) : laurentTube f D :=
  ⟨laurentSegmentCurve f (p.1.val - b, p.2.val) 1,
    ((laurentSegmentCurve_spec f (convexTransport_admissible hD hc hb p.1 p.2)
      1 (by simp)).1).1, by
      have he := laurentSegmentCurve_base f (convexTransport_admissible hD hc hb p.1 p.2)
        (by simp : (1 : ℝ) ∈ Icc 0 1)
      rw [he]
      simpa only [one_smul, p.2.property.2, add_sub_cancel] using p.1.property⟩

/-- Base evaluation together with straight transport back to the reference fiber. -/
def convexTransportBack (y : laurentTube f D) : D × LaurentFiber f b :=
  (⟨laurentEval f y.val, y.property.2⟩,
    ⟨laurentSegmentCurve f (b - laurentEval f y.val, y.val) 1,
      ((laurentSegmentCurve_spec f (convexTransportBack_admissible hD hc hb y)
        1 (by simp)).1).1, by
        simpa only [one_smul, add_sub_cancel] using
          laurentSegmentCurve_base f (convexTransportBack_admissible hD hc hb y)
            (by simp : (1 : ℝ) ∈ Icc 0 1)⟩)

@[simp] theorem convexTransport_base (p : D × LaurentFiber f b) :
    laurentEval f (convexTransport hD hc hb p).val = p.1.val := by
  simpa only [convexTransport, one_smul, p.2.property.2, add_sub_cancel] using
    laurentSegmentCurve_base f (convexTransport_admissible hD hc hb p.1 p.2)
      (by simp : (1 : ℝ) ∈ Icc 0 1)

theorem convexTransport_left_inv (p : D × LaurentFiber f b) :
    convexTransportBack hD hc hb (convexTransport hD hc hb p) = p := by
  apply Prod.ext
  · exact Subtype.ext (convexTransport_base hD hc hb p)
  · apply Subtype.ext
    change laurentSegmentCurve f
      (b - laurentEval f (convexTransport hD hc hb p).val,
        (convexTransport hD hc hb p).val) 1 = p.2.val
    rw [convexTransport_base]
    have he : b - p.1.val = -(p.1.val - b) := by abel
    rw [he]
    exact laurentSegmentCurve_reverse_endpoint f (convexTransport_admissible hD hc hb p.1 p.2)

theorem convexTransport_right_inv (y : laurentTube f D) :
    convexTransport hD hc hb (convexTransportBack hD hc hb y) = y := by
  apply Subtype.ext
  change laurentSegmentCurve f
    (laurentEval f y.val - b, laurentSegmentCurve f (b - laurentEval f y.val, y.val) 1) 1 = y.val
  have he : laurentEval f y.val - b = -(b - laurentEval f y.val) := by abel
  rw [he]
  exact laurentSegmentCurve_reverse_endpoint f (convexTransportBack_admissible hD hc hb y)

/-- The bijection underlying the local product structure, including empty fibers. -/
def convexTransportEquiv : (D × LaurentFiber f b) ≃ laurentTube f D where
  toFun := convexTransport hD hc hb
  invFun := convexTransportBack hD hc hb
  left_inv := convexTransport_left_inv hD hc hb
  right_inv := convexTransport_right_inv hD hc hb

/-- At the reference value the product trivialization is the identity on its fiber. -/
theorem convexTransport_center (z : LaurentFiber f b) :
    (convexTransport hD hc hb (⟨b, hb⟩, z)).val = z.val := by
  have hp : (0, z.val) ∈ admissibleSegmentParameters f := by
    simpa only [sub_self] using convexTransport_admissible hD hc hb ⟨b, hb⟩ z
  change laurentSegmentCurve f (b - b, z.val) 1 = z.val
  rw [sub_self]
  exact (laurentSegmentCurve_eq_fiberCurve hp.2 ⟨z.val, hp.1, rfl⟩ (by simp)).trans
    (fiberTransport_zero hp.2 ⟨z.val, hp.1, rfl⟩)

end ConvexTube

/-- An open torus preimage, carrying its usual open-submanifold structure. -/
def laurentTubeOpen {d : ℕ} (f : MultiLaurent d) (D : TopologicalSpace.Opens ℂ) :
    TopologicalSpace.Opens (Fin d → ℂ) :=
  ⟨laurentTube f D, laurentTube_isOpen f D.isOpen⟩

/-- Smoothness into a regular fiber follows from smoothness of the ambient map. -/
theorem regularFiber_contMDiff_of_val {d : ℕ} (f : MultiLaurent d) (s : ℂ)
    [Fact (RegularLaurentValue f s)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} (g : M → LaurentFiber f s)
    (hg : ContMDiff I (modelWithCornersSelf ℝ (Fin d → ℂ)) n (fun x => (g x).val)) :
    ContMDiff I (modelWithCornersSelf ℝ (LaurentFiberModel d)) n g := by
  intro x
  apply contMDiffAt_iff_target.mpr
  refine ⟨(hg.continuous.subtype_mk _).continuousAt, ?_⟩
  have hchart : ContDiffAt ℝ n (fun y => (regularFiberProductChart f s (g x) y).2) (g x).val :=
    (((regularFiberProductChart_spec f s (g x)).2.2.2.1.contDiffAt
      ((regularFiberProductChart f s (g x)).open_source.mem_nhds
        (regularFiberProductChart_spec f s (g x)).1)).snd).of_le le_top
  have hh := hchart.contMDiffAt.comp x (hg x)
  simpa only [extChartAt, OpenPartialHomeomorph.extend, mfld_simps, chartAt_regularFiber,
    regularFiberChart, fiberSliceChart_apply, Function.comp_def] using hh

section SmoothTube
variable {d : ℕ} {f : MultiLaurent d} {D : TopologicalSpace.Opens ℂ} {b : ℂ}
variable (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D)
variable [Fact (RegularLaurentValue f b)]

/-- The product-to-tube transport is smooth on the whole base times the fiber. -/
theorem convexTransport_contMDiff :
    ContMDiff (M := D × LaurentFiber f b) (M' := laurentTubeOpen f D)
      ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (LaurentFiberModel d)))
      (modelWithCornersSelf ℝ (Fin d → ℂ)) ∞
      (convexTransport hD hc hb : D × LaurentFiber f b → laurentTubeOpen f D) := by
  apply (ContMDiff.subtypeVal_comp_iff (laurentTubeOpen f D) _).mp
  have hs : ContMDiff ((modelWithCornersSelf ℝ ℂ).prod
      (modelWithCornersSelf ℝ (LaurentFiberModel d))) (modelWithCornersSelf ℝ ℂ) ∞
      (fun p : D × LaurentFiber f b => p.1.val - b) :=
    (contDiff_id.sub contDiff_const).comp_contMDiff
      (contMDiff_subtype_val.comp contMDiff_fst)
  have hz := ((regularFiber_val_contMDiff f b).of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).comp
    (contMDiff_snd (I := modelWithCornersSelf ℝ ℂ) (M := D))
  exact ((laurentSegmentCurve_endpoint_analytic f).of_le le_top).contMDiffOn.comp_contMDiff
    (hs.prodMk_space hz) (fun p => convexTransport_admissible hD hc hb p.1 p.2)

/-- Evaluation is smooth on the open tube. -/
theorem laurentTube_eval_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (Fin d → ℂ)) (modelWithCornersSelf ℝ ℂ) ∞
      (fun y : laurentTubeOpen f D => laurentEval f y.val) := by
  intro y
  exact contMDiffAt_subtype_iff.mpr
    (((laurentEval_contDiffAt f y.property.1).of_le le_top).contMDiffAt)

/-- The inverse product coordinates are smooth, including their fiber component. -/
theorem convexTransportBack_contMDiff :
    ContMDiff (M := laurentTubeOpen f D) (M' := D × LaurentFiber f b)
      (modelWithCornersSelf ℝ (Fin d → ℂ))
      ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (LaurentFiberModel d))) ∞
      (convexTransportBack hD hc hb : laurentTubeOpen f D → D × LaurentFiber f b) := by
  have hs : ContMDiff (M' := D) (modelWithCornersSelf ℝ (Fin d → ℂ)) (modelWithCornersSelf ℝ ℂ) ∞
      (fun y : laurentTubeOpen f D => (convexTransportBack hD hc hb y).1) :=
    (ContMDiff.subtypeVal_comp_iff D _).mp laurentTube_eval_contMDiff
  have ha : ContMDiff (modelWithCornersSelf ℝ (Fin d → ℂ)) (modelWithCornersSelf ℝ ℂ) ∞
      (fun y : laurentTubeOpen f D => b - laurentEval f y.val) :=
    (contDiff_const.sub contDiff_id).comp_contMDiff laurentTube_eval_contMDiff
  have hz : ContMDiff (modelWithCornersSelf ℝ (Fin d → ℂ))
      (modelWithCornersSelf ℝ (Fin d → ℂ)) ∞
      (fun y : laurentTubeOpen f D => (convexTransportBack hD hc hb y).2.val) :=
    ((laurentSegmentCurve_endpoint_analytic f).of_le le_top).contMDiffOn.comp_contMDiff
      (ha.prodMk_space contMDiff_subtype_val)
      (fun y => convexTransportBack_admissible hD hc hb y)
  exact hs.prodMk (regularFiber_contMDiff_of_val f b _ hz)

end SmoothTube

/-- A good base consists of regular values. -/
theorem GoodBase.regularValue {d : ℕ} {f : MultiLaurent d} {D : Set ℂ}
    (hD : GoodBase f D) {b : ℂ} (hb : b ∈ D) : RegularLaurentValue f b :=
  regularLaurentValue_of_not_critical f (fun h => hD b hb (Or.inl h))

/-- The manuscript's product trivialization on a convex open good base. Its
regular-fiber instance is derived from the stated exclusion hypothesis. -/
def convexTransportDiffeomorph {d : ℕ} {f : MultiLaurent d}
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D) :
    letI : Fact (RegularLaurentValue f b) := ⟨hD.regularValue hb⟩
    Diffeomorph ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (LaurentFiberModel d)))
      (modelWithCornersSelf ℝ (Fin d → ℂ)) (D × LaurentFiber f b) (laurentTubeOpen f D) ∞ := by
  letI : Fact (RegularLaurentValue f b) := ⟨hD.regularValue hb⟩
  exact { toEquiv := convexTransportEquiv hD hc hb
          contMDiff_toFun := convexTransport_contMDiff hD hc hb
          contMDiff_invFun := convexTransportBack_contMDiff hD hc hb }

/-- The trivialization lies over the identity on the base. -/
theorem convexTransportDiffeomorph_base {d : ℕ} {f : MultiLaurent d}
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D)
    (p : D × LaurentFiber f b) :
    laurentEval f (convexTransportDiffeomorph hD hc hb p).val = p.1.val :=
  convexTransport_base hD hc hb p

/-- Sweeping any compact family by the trivialization remains compact in the
regular torus; this applies in particular to a compact base times a compact cycle. -/
theorem convexTransport_compact_sweep {d : ℕ} {f : MultiLaurent d}
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D)
    (K : Set (D × LaurentFiber f b)) (hK : IsCompact K) :
    IsCompact ((fun p => (convexTransport hD hc hb p).val) '' K) ∧
      ((fun p => (convexTransport hD hc hb p).val) '' K) ⊆ laurentRegularDomain f := by
  let : Fact (RegularLaurentValue f b) := ⟨hD.regularValue hb⟩
  refine ⟨hK.image (continuous_subtype_val.comp
    (convexTransportDiffeomorph hD hc hb).continuous), ?_⟩
  rintro y ⟨p, hp, rfl⟩
  exact (laurentSegmentCurve_spec f (convexTransport_admissible hD hc hb p.1 p.2)
    1 (by simp)).1

/-- Each point of any open good base has a smooth product neighborhood. The
finiteness of the critical-value sets is a separate manuscript dependency. -/
theorem laurent_local_trivialization {d : ℕ} (f : MultiLaurent d)
    (U : TopologicalSpace.Opens ℂ) (hU : GoodBase f U) {b : ℂ} (hb : b ∈ U) :
    letI : Fact (RegularLaurentValue f b) := ⟨hU.regularValue hb⟩
    ∃ D : TopologicalSpace.Opens ℂ, b ∈ D ∧ (D : Set ℂ) ⊆ U ∧ Convex ℝ (D : Set ℂ) ∧
      ∃ e : Diffeomorph
        ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (LaurentFiberModel d)))
        (modelWithCornersSelf ℝ (Fin d → ℂ)) (D × LaurentFiber f b) (laurentTubeOpen f D) ∞,
        ∀ p : D × LaurentFiber f b, laurentEval f (e p).val = p.1.val := by
  let : Fact (RegularLaurentValue f b) := ⟨hU.regularValue hb⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp U.isOpen b hb
  let D : TopologicalSpace.Opens ℂ := ⟨Metric.ball b r, Metric.isOpen_ball⟩
  have hbD : b ∈ D := Metric.mem_ball_self hr
  have hD : GoodBase f D := fun s hs => hU s (hrU hs)
  have hc : Convex ℝ (D : Set ℂ) := convex_ball b r
  exact ⟨D, hbD, hrU, hc, convexTransportDiffeomorph hD hc hbD,
    convexTransportDiffeomorph_base hD hc hbD⟩

/-- Closedness follows from proper-radius compactness, independently of the
common-radius finiteness theorem, which remains a separate obligation. -/
theorem laurentCriticalValues_isClosed {d : ℕ} (f : MultiLaurent d) :
    IsClosed (ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :=
  criticalValues_union_isClosed _ _ _ (laurentOnAffineTorus_continuous f)
    (laurentDifferentialNorm_continuous f) (fun _ => norm_nonneg _)
    (laurentDifferentialNorm_nonneg f) (affineTorus_sublevel_isCompact d)

/-- The actual complement of the two manuscript critical-value sets is open. -/
def laurentGoodValues {d : ℕ} (f : MultiLaurent d) : TopologicalSpace.Opens ℂ :=
  ⟨(ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f))ᶜ, (laurentCriticalValues_isClosed f).isOpen_compl⟩

theorem laurentGoodValues_good {d : ℕ} (f : MultiLaurent d) : GoodBase f (laurentGoodValues f) :=
  fun _ h => h

/-- Local smooth triviality over the actual good-value locus, with no extra
openness or finiteness hypothesis. Finiteness is not a conclusion of this theorem. -/
theorem laurent_local_trivialization_at {d : ℕ} (f : MultiLaurent d) {b : ℂ}
    (hb : b ∈ laurentGoodValues f) :
    letI : Fact (RegularLaurentValue f b) := ⟨(laurentGoodValues_good f).regularValue hb⟩
    ∃ D : TopologicalSpace.Opens ℂ, b ∈ D ∧ GoodBase f D ∧ Convex ℝ (D : Set ℂ) ∧
      ∃ e : Diffeomorph
        ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (LaurentFiberModel d)))
        (modelWithCornersSelf ℝ (Fin d → ℂ)) (D × LaurentFiber f b) (laurentTubeOpen f D) ∞,
        ∀ p : D × LaurentFiber f b, laurentEval f (e p).val = p.1.val := by
  let : Fact (RegularLaurentValue f b) := ⟨(laurentGoodValues_good f).regularValue hb⟩
  obtain ⟨D, hbD, hDU, hc, e, he⟩ :=
    laurent_local_trivialization f (laurentGoodValues f) (laurentGoodValues_good f) hb
  exact ⟨D, hbD, fun s hs => laurentGoodValues_good f s (hDU hs), hc, e, he⟩

end
end DuistermaatVanDerKallen
