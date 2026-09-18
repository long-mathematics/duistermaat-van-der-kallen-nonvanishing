import DuistermaatVanDerKallen.DrivenAnalytic
import DuistermaatVanDerKallen.DrivenTransport
import DuistermaatVanDerKallen.FiberDiffeomorph

/-! Complete analytic endpoint diffeomorphisms along prescribed C¹ base paths. -/

open Set Filter
open scoped Topology Manifold

namespace DuistermaatVanDerKallen
noncomputable section

/-- A C¹ unit-interval base path with specified endpoints, avoiding exactly the
ordinary and asymptotic critical values of the manuscript's proper geometry. -/
structure LaurentC1Path {d : ℕ} (f : MultiLaurent d) (s t : ℂ) where
  base : ℝ → ℂ
  velocity : ℝ → ℂ
  velocity_continuous : ContinuousOn velocity (Icc (0 : ℝ) 1)
  base_deriv : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivWithinAt base (velocity r) (Icc 0 1) r
  base_zero : base 0 = s
  base_one : base 1 = t
  good : ∀ r ∈ Icc (0 : ℝ) 1, base r ∉
    ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f)

namespace LaurentC1Path
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

/-- A straight base segment presented as a C¹ path with matching endpoints. -/
def line {d : ℕ} {f : MultiLaurent d} {s t : ℂ}
    (h : GoodSegment f s (t - s)) : LaurentC1Path f s t where
  base r := s + r • (t - s)
  velocity _ := t - s
  velocity_continuous := continuousOn_const
  base_deriv r _ := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id r).smul_const (t - s)).const_add s).hasDerivWithinAt
  base_zero := by simp
  base_one := by simp
  good := h

theorem line_base_mem {d : ℕ} {f : MultiLaurent d} {s t : ℂ}
    (h : GoodSegment f s (t - s)) {D : Set ℂ} (hc : Convex ℝ D)
    (hs : s ∈ D) (ht : t ∈ D) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (line h).base r ∈ D := by
  simpa only [line, AffineMap.lineMap_apply_module', add_comm] using hc.lineMap_mem hs ht hr

/-- Normalize a C¹ piece on any nondecreasing compact real interval to unit
time, scaling the velocity by the interval length. -/
def ofInterval (α v : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b))
    (hα : ∀ r ∈ Icc a b, HasDerivWithinAt α (v r) (Icc a b) r)
    (hgood : ∀ r ∈ Icc a b, α r ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) : LaurentC1Path f (α a) (α b) := by
  have hmap : MapsTo (fun r : ℝ => a + (b - a) * r) (Icc 0 1) (Icc a b) := by
    intro r hr
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hr.1,
      mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hr.2)]
  refine { base := fun r => α (a + (b - a) * r)
           velocity := fun r => (b - a) • v (a + (b - a) * r)
           velocity_continuous := ?_
           base_deriv := ?_
           base_zero := by simp
           base_one := by simp
           good := fun r hr => hgood _ (hmap hr) }
  · exact (show ContinuousOn (fun _ : ℝ => b - a) (Icc 0 1) from continuousOn_const).smul
      (hv.comp (by fun_prop) hmap)
  · intro r hr
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hα _ (hmap hr)).scomp r
        (((hasDerivAt_id r).const_mul (b - a)).const_add a).hasDerivWithinAt hmap

/-- Reversal retains the exact path hypothesis and reverses the scalar velocity. -/
def reverse (h : LaurentC1Path f s t) : LaurentC1Path f t s where
  base r := h.base (1 - r)
  velocity r := -h.velocity (1 - r)
  velocity_continuous := h.velocity_continuous.comp
    (show ContinuousOn (fun r : ℝ => 1 - r) (Icc 0 1) from
      (continuous_const.sub continuous_id).continuousOn)
    (fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩) |>.neg
  base_deriv := by
    intro r hr
    have hmem : MapsTo (fun r : ℝ => 1 - r) (Icc 0 1) (Icc 0 1) :=
      fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩
    simpa only [Function.comp_def, neg_smul, one_smul] using
      (h.base_deriv (1 - r) (hmem hr)).scomp r
        ((hasDerivAt_id r).const_sub 1).hasDerivWithinAt hmem
  base_zero := by simpa using h.base_one
  base_one := by simpa using h.base_zero
  good := fun r hr => h.good (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩

@[simp] theorem reverse_reverse (h : LaurentC1Path f s t) : h.reverse.reverse = h := by
  cases h
  simp only [reverse, sub_sub_cancel, neg_neg]

/-- All fibers met by this path carry the regular-fiber manifold structure. -/
theorem regularValue (h : LaurentC1Path f s t) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    RegularLaurentValue f (h.base r) :=
  regularLaurentValue_of_not_critical f (fun hc => h.good r hr (Or.inl hc))

theorem start_regular (h : LaurentC1Path f s t) : RegularLaurentValue f s := by
  simpa only [h.base_zero] using h.regularValue (by simp : (0 : ℝ) ∈ Icc 0 1)

theorem end_regular (h : LaurentC1Path f s t) : RegularLaurentValue f t := by
  simpa only [h.base_one] using h.regularValue (by simp : (1 : ℝ) ∈ Icc 0 1)

/-- The complete driven lift, with exact base motion, for each initial fiber point. -/
theorem curve_exists (h : LaurentC1Path f s t) (z : LaurentFiber f s) :
    ∃ γ : ℝ → Fin d → ℂ, γ 0 = z.val ∧
      ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (h.velocity r) (γ r)) r ∧
        laurentEval f (γ r) = h.base r :=
  laurent_complete_C1_path f h.base h.velocity h.velocity_continuous h.base_deriv z.val
    z.property.1 (z.property.2.trans h.base_zero.symm) h.good

def curve (h : LaurentC1Path f s t) (z : LaurentFiber f s) : ℝ → Fin d → ℂ :=
  (h.curve_exists z).choose

theorem curve_spec (h : LaurentC1Path f s t) (z : LaurentFiber f s) :
    h.curve z 0 = z.val ∧ ∀ r ∈ Icc (0 : ℝ) 1,
      h.curve z r ∈ laurentRegularDomain f ∧
        HasDerivAt (h.curve z) (laurentVectorField f (h.velocity r) (h.curve z r)) r ∧
        laurentEval f (h.curve z r) = h.base r :=
  (h.curve_exists z).choose_spec

/-- Endpoint transport along the complete normalized-gradient trajectory. -/
def transport (h : LaurentC1Path f s t) (z : LaurentFiber f s) : LaurentFiber f t :=
  ⟨h.curve z 1, ((h.curve_spec z).2 1 (by simp)).1.1,
    ((h.curve_spec z).2 1 (by simp)).2.2.trans h.base_one⟩

/-- The reversed chosen trajectory agrees with the original trajectory run
backwards. This removes dependence on the existence witnesses. -/
theorem reverse_curve (h : LaurentC1Path f s t) (z : LaurentFiber f s) :
    EqOn (h.reverse.curve (h.transport z)) (fun r => h.curve z (1 - r)) (Icc (0 : ℝ) 1) := by
  apply laurent_driven_unit_unique f h.reverse.velocity h.reverse.velocity_continuous
    (fun r hr => ⟨((h.reverse.curve_spec (h.transport z)).2 r hr).1,
      ((h.reverse.curve_spec (h.transport z)).2 r hr).2.1⟩)
  · intro r hr
    have hr' : 1 - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    refine ⟨((h.curve_spec z).2 (1 - r) hr').1, ?_⟩
    have hd := ((h.curve_spec z).2 (1 - r) hr').2.1.scomp r ((hasDerivAt_id r).const_sub 1)
    simpa only [reverse, laurentVectorField_neg, neg_smul, one_smul, Function.comp_def] using hd
  · simpa only [sub_zero, transport] using (h.reverse.curve_spec (h.transport z)).1

@[simp] theorem transport_left_inv (h : LaurentC1Path f s t) (z : LaurentFiber f s) :
    h.reverse.transport (h.transport z) = z := by
  apply Subtype.ext
  simpa only [transport, sub_self, (h.curve_spec z).1] using h.reverse_curve z (by simp : (1 : ℝ) ∈ Icc 0 1)

@[simp] theorem transport_right_inv (h : LaurentC1Path f s t) (z : LaurentFiber f t) :
    h.transport (h.reverse.transport z) = z := by
  simpa only [reverse_reverse] using h.reverse.transport_left_inv z

/-- The endpoint bijection is inverted by the reversed prescribed path. -/
def transportEquiv (h : LaurentC1Path f s t) : LaurentFiber f s ≃ LaurentFiber f t where
  toFun := h.transport
  invFun := h.reverse.transport
  left_inv := h.transport_left_inv
  right_inv := h.transport_right_inv

/-- Ambient totalization for proving initial-point analyticity. No trajectory
claim is made outside the starting fiber. -/
def ambientCurve (h : LaurentC1Path f s t) (z : Fin d → ℂ) : ℝ → Fin d → ℂ := by
  classical
  exact if hz : (∀ i, z i ≠ 0) ∧ laurentEval f z = s then h.curve ⟨z, hz⟩ else fun _ => z

@[simp] theorem ambientCurve_zero (h : LaurentC1Path f s t) (z : Fin d → ℂ) :
    h.ambientCurve z 0 = z := by
  unfold ambientCurve
  split_ifs with hz
  · exact (h.curve_spec ⟨z, hz⟩).1
  · rfl

theorem ambientCurve_eq (h : LaurentC1Path f s t) (z : LaurentFiber f s) :
    h.ambientCurve z.val = h.curve z := by
  simp only [ambientCurve, dite_eq_left z.property]

/-- The whole complete trajectory is analytic in its initial point at each
fixed time, within the actual starting fiber. -/
theorem ambientCurve_analytic (h : LaurentC1Path f s t) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ ⊤ (fun z => h.ambientCurve z r)
      {z | (∀ i, z i ≠ 0) ∧ laurentEval f z = s} := by
  intro z hz
  apply laurent_driven_family_analytic_on f h.velocity h.velocity_continuous hz _ _ r hr
  · intro y hy u hu
    rw [h.ambientCurve_eq ⟨y, hy⟩]
    exact ⟨((h.curve_spec ⟨y, hy⟩).2 u hu).1, ((h.curve_spec ⟨y, hy⟩).2 u hu).2.1⟩
  · simp only [ambientCurve_zero]
    exact contDiffWithinAt_id

/-- Fixed-time dependence is continuous on the original fiber topology. -/
theorem curve_continuous (h : LaurentC1Path f s t) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    Continuous (fun z : LaurentFiber f s => h.curve z r) := by
  have hc := continuousOn_iff_continuous_domRestrict.mp (h.ambientCurve_analytic hr).continuousOn
  change Continuous (fun z : LaurentFiber f s => h.ambientCurve z.val r) at hc
  simpa only [ambientCurve_eq] using hc

theorem transport_continuous (h : LaurentC1Path f s t) : Continuous h.transport :=
  (h.curve_continuous (by simp : (1 : ℝ) ∈ Icc 0 1)).subtype_mk _

/-- Endpoint transport is analytic for the actual regular-fiber manifolds. -/
theorem transport_contMDiff (h : LaurentC1Path f s t)
    [Fact (RegularLaurentValue f s)] [Fact (RegularLaurentValue f t)] :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ h.transport := by
  apply regularFiber_map_contMDiff_of_extensions f s t h.transport h.transport_continuous
  intro z
  obtain ⟨G, heq, hG⟩ := analyticWithinAt_iff_exists_analyticAt.mp
    ((h.ambientCurve_analytic (by simp : (1 : ℝ) ∈ Icc 0 1) z.val z.property).analyticWithinAt)
  refine ⟨G, hG, ?_⟩
  have hv : Tendsto (Subtype.val : LaurentFiber f s → Fin d → ℂ) (𝓝 z)
      (𝓝[{y | (∀ i, y i ≠ 0) ∧ laurentEval f y = s}] z.val) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.continuousAt,
      Filter.Eventually.of_forall (fun y => y.property)⟩
  have heq' := heq.filter_mono (nhdsWithin_mono _ (subset_insert _ _))
  filter_upwards [hv.eventually heq'] with y hy
  simpa only [ambientCurve_eq, transport] using hy

/-- The complete endpoint map is a real analytic diffeomorphism. All regular
fiber hypotheses are derived from the path's critical-value exclusion. -/
def transportDiffeomorph (h : LaurentC1Path f s t) :
    letI : Fact (RegularLaurentValue f s) := ⟨h.start_regular⟩
    letI : Fact (RegularLaurentValue f t) := ⟨h.end_regular⟩
    Diffeomorph (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) (LaurentFiber f s) (LaurentFiber f t) ⊤ := by
  letI : Fact (RegularLaurentValue f s) := ⟨h.start_regular⟩
  letI : Fact (RegularLaurentValue f t) := ⟨h.end_regular⟩
  exact { toEquiv := h.transportEquiv
          contMDiff_toFun := h.transport_contMDiff
          contMDiff_invFun := h.reverse.transport_contMDiff }

end LaurentC1Path
end
end DuistermaatVanDerKallen
