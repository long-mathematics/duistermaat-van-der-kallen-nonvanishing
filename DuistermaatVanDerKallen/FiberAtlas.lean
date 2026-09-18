import DuistermaatVanDerKallen.RegularFiberCharts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Fiber charts obtained by slicing regular analytic product charts. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

section Slice

variable {d : ℕ} {f : MultiLaurent d} {s : ℂ}
variable (e : OpenPartialHomeomorph (Fin d → ℂ) (ℂ × LaurentFiberModel d))
variable (hreg : e.source ⊆ laurentRegularDomain f)
variable (hfst : ∀ y, (e y).1 = laurentEval f y)
variable (z : LaurentFiber f s)

/-- Totalized inverse of the slice of a product chart at the fixed fiber value. -/
def fiberSliceInverse (k : LaurentFiberModel d) : LaurentFiber f s := by
  classical
  exact if hk : (s, k) ∈ e.target then
    ⟨e.symm (s, k), (hreg (e.map_target hk)).1, by
      rw [← hfst]
      exact congrArg Prod.fst (e.right_inv hk)⟩
  else z

theorem fiberSliceInverse_val {k : LaurentFiberModel d} (hk : (s, k) ∈ e.target) :
    (fiberSliceInverse e hreg hfst z k).val = e.symm (s, k) := by
  simp only [fiberSliceInverse, dite_eq_left hk]

/-- The slice is an actual open partial homeomorphism from the fiber to its
fixed Euclidean model. -/
def fiberSliceChart : OpenPartialHomeomorph (LaurentFiber f s) (LaurentFiberModel d) where
  toFun y := (e y.val).2
  invFun := fiberSliceInverse e hreg hfst z
  source := {y | y.val ∈ e.source}
  target := {k | (s, k) ∈ e.target}
  map_source' := by
    intro y hy
    have he : e y.val = (s, (e y.val).2) := Prod.ext ((hfst y.val).trans y.property.2) rfl
    change (s, (e y.val).2) ∈ e.target
    rw [← he]
    exact e.map_source hy
  map_target' := by
    intro k hk
    change (fiberSliceInverse e hreg hfst z k).val ∈ e.source
    rw [fiberSliceInverse_val e hreg hfst z hk]
    exact e.map_target hk
  left_inv' := by
    intro y hy
    have he : e y.val = (s, (e y.val).2) := Prod.ext ((hfst y.val).trans y.property.2) rfl
    have hk : (s, (e y.val).2) ∈ e.target := he ▸ e.map_source hy
    apply Subtype.ext
    rw [fiberSliceInverse_val e hreg hfst z hk, ← he, e.left_inv hy]
  right_inv' := by
    intro k hk
    rw [fiberSliceInverse_val e hreg hfst z hk, e.right_inv hk]
  continuousOn_toFun :=
    (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h)).snd
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.2
    have hc : Continuous (fun k : {k : LaurentFiberModel d | (s, k) ∈ e.target} =>
        e.symm (s, k.val)) :=
      e.symm.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun k => k.property)
    have hv : Continuous (fun k : {k : LaurentFiberModel d | (s, k) ∈ e.target} =>
        (fiberSliceInverse e hreg hfst z k.val).val) := by
      convert hc using 1
      funext k
      exact fiberSliceInverse_val e hreg hfst z k.property
    exact hv.subtype_mk _
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)

theorem fiberSliceChart_source :
    (fiberSliceChart e hreg hfst z).source = {y | y.val ∈ e.source} := rfl

theorem fiberSliceChart_target :
    (fiberSliceChart e hreg hfst z).target = {k | (s, k) ∈ e.target} := rfl

theorem fiberSliceChart_apply (y : LaurentFiber f s) :
    fiberSliceChart e hreg hfst z y = (e y.val).2 := rfl

theorem fiberSliceChart_symm_val {k : LaurentFiberModel d}
    (hk : k ∈ (fiberSliceChart e hreg hfst z).target) :
    ((fiberSliceChart e hreg hfst z).symm k).val = e.symm (s, k) :=
  fiberSliceInverse_val e hreg hfst z hk

/-- The inverse fiber chart, viewed in the ambient coordinates, is analytic
throughout its open model domain. -/
theorem fiberSliceChart_inverse_contDiffOn
    (he : ContDiffOn ℝ ⊤ e.symm e.target) :
    ContDiffOn ℝ ⊤ (fun k => ((fiberSliceChart e hreg hfst z).symm k).val)
      (fiberSliceChart e hreg hfst z).target := by
  have h : ContDiffOn ℝ ⊤ (fun k : LaurentFiberModel d => e.symm (s, k))
      (fiberSliceChart e hreg hfst z).target :=
    he.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hk => hk)
  apply h.congr
  intro k hk
  exact fiberSliceChart_symm_val e hreg hfst z hk

end Slice

/-- Every point of the fiber lies in the regular torus domain. This is an
explicit property of the Laurent polynomial and value, not an extra axiom. -/
def RegularLaurentValue {d : ℕ} (f : MultiLaurent d) (s : ℂ) : Prop :=
  ∀ z : LaurentFiber f s, z.val ∈ laurentRegularDomain f

/-- Every good base segment starts at a regular fiber. -/
theorem GoodSegment.regularValue {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : RegularLaurentValue f s := by
  intro z
  simpa only [(fiberCurve_spec h z).1] using ((fiberCurve_spec h z).2 0 (by simp)).1

/-- Excluding ordinary critical values suffices for the manifold hypothesis. -/
theorem regularLaurentValue_of_not_critical {d : ℕ} (f : MultiLaurent d) {s : ℂ}
    (hs : s ∉ ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f)) :
    RegularLaurentValue f s := by
  intro z
  refine ⟨z.property.1, ?_⟩
  intro hz
  have hnorm : laurentDifferentialNorm f ⟨torusEmbed z.val, embed_mem z.property.1⟩ = 0 := by
    have he := laurentDifferentialNorm_sq f z.property.1
    rw [hz] at he
    exact (sq_eq_zero_iff).mp he
  apply hs
  exact ⟨⟨torusEmbed z.val, embed_mem z.property.1⟩, hnorm,
    (laurentOnAffineTorus_embed f z.property.1).trans z.property.2⟩

section Atlas

variable {d : ℕ} (f : MultiLaurent d) (s : ℂ) [Fact (RegularLaurentValue f s)]

/-- A chosen analytic product chart at each point of a regular fiber. -/
def regularFiberProductChart (z : LaurentFiber f s) :
    OpenPartialHomeomorph (Fin d → ℂ) (ℂ × LaurentFiberModel d) :=
  (laurent_regular_product_chart_fixed f (Fact.out (p := RegularLaurentValue f s) z)).choose

theorem regularFiberProductChart_spec (z : LaurentFiber f s) :
    z.val ∈ (regularFiberProductChart f s z).source ∧
      (regularFiberProductChart f s z).source ⊆ laurentRegularDomain f ∧
      (∀ y, (regularFiberProductChart f s z y).1 = laurentEval f y) ∧
      ContDiffOn ℝ ⊤ (regularFiberProductChart f s z) (regularFiberProductChart f s z).source ∧
      ContDiffOn ℝ ⊤ (regularFiberProductChart f s z).symm (regularFiberProductChart f s z).target :=
  (laurent_regular_product_chart_fixed f (Fact.out (p := RegularLaurentValue f s) z)).choose_spec

/-- The preferred fiber chart is the fixed-value slice of its product chart. -/
def regularFiberChart (z : LaurentFiber f s) :
    OpenPartialHomeomorph (LaurentFiber f s) (LaurentFiberModel d) :=
  fiberSliceChart (regularFiberProductChart f s z)
    (regularFiberProductChart_spec f s z).2.1 (regularFiberProductChart_spec f s z).2.2.1 z

/-- Chart changes are analytic on the entire overlap. -/
theorem regularFiberChart_transition (z w : LaurentFiber f s) :
    ContDiffOn ℝ ⊤ ((regularFiberChart f s z).symm.trans (regularFiberChart f s w))
      ((regularFiberChart f s z).symm.trans (regularFiberChart f s w)).source := by
  have hinv := fiberSliceChart_inverse_contDiffOn (regularFiberProductChart f s z)
    (regularFiberProductChart_spec f s z).2.1 (regularFiberProductChart_spec f s z).2.2.1 z
    (regularFiberProductChart_spec f s z).2.2.2.2
  exact ((regularFiberProductChart_spec f s w).2.2.2.1.snd).comp
    (hinv.mono (fun _ hk => hk.1)) (fun _ hk => hk.2)

/-- The atlas is built from the proved regular-level charts, retaining the
existing subtype topology on the fiber. -/
instance regularFiberChartedSpace : ChartedSpace (LaurentFiberModel d) (LaurentFiber f s) where
  atlas := Set.range (regularFiberChart f s)
  chartAt := regularFiberChart f s
  mem_chart_source z := (regularFiberProductChart_spec f s z).1
  chart_mem_atlas z := ⟨z, rfl⟩

@[simp] theorem chartAt_regularFiber (z : LaurentFiber f s) :
    chartAt (LaurentFiberModel d) z = regularFiberChart f s z := rfl

/-- Every regular Laurent fiber is an analytic real manifold of dimension
`2d - 2`; empty fibers require no separate choice of a reference point. -/
instance regularFiberIsManifold :
    IsManifold (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ (LaurentFiber f s) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨z, rfl⟩
  rcases he' with ⟨w, rfl⟩
  simpa only [mfld_simps] using regularFiberChart_transition f s z w

/-- Inclusion of a regular fiber in its ambient coordinate space is analytic. -/
theorem regularFiber_val_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (Fin d → ℂ)) ⊤ (Subtype.val : LaurentFiber f s → Fin d → ℂ) := by
  intro z
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hi := fiberSliceChart_inverse_contDiffOn (regularFiberProductChart f s z)
    (regularFiberProductChart_spec f s z).2.1 (regularFiberProductChart_spec f s z).2.2.1 z
    (regularFiberProductChart_spec f s z).2.2.2.2
  have hz : regularFiberChart f s z z ∈ (regularFiberChart f s z).target :=
    (regularFiberChart f s z).map_source (regularFiberProductChart_spec f s z).1
  have hh := hi.contDiffAt ((regularFiberChart f s z).open_target.mem_nhds hz)
  simpa only [mfld_simps, chartAt_self_eq, chartAt_regularFiber, regularFiberChart,
    OpenPartialHomeomorph.refl_apply, Function.comp_def] using hh.contDiffWithinAt (s := Set.univ)

end Atlas

end

end DuistermaatVanDerKallen
