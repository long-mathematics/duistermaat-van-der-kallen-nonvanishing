import DuistermaatVanDerKallen.HomologySheaf

/-! Homology maps at each time of a complete ODE trajectory, with locally
constant coordinates near every time. -/

open Set CategoryTheory AlgebraicTopology TopologicalSpace
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section
namespace LaurentC1Path
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

def timeMap (h : LaurentC1Path f s t) (u : CurveTime) :
    C(LaurentFiber f s, LaurentFiber f (h.base u)) :=
  ⟨fun z => ⟨h.curve z u, ((h.curve_spec z).2 u u.property).1.1,
      ((h.curve_spec z).2 u u.property).2.2⟩,
    (h.curves_continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩

def timeHomologyMap (h : LaurentC1Path f s t) (n : ℕ) (u : CurveTime) :
    laurentFiberHomology f s n ⟶ laurentFiberHomology f (h.base u) n :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom (h.timeMap u))

def timeCoordinateHomotopy (h : LaurentC1Path f s t)
    (P : LaurentHomologyPatch f) (a b : CurveTime)
    (ha : h.base a ∈ P.domain) (hb : h.base b ∈ P.domain)
    (hp : ∀ r : CurveTime, h.base (AffineMap.lineMap a.val b.val r.val) ∈ P.domain) :
    ContinuousMap.Homotopy
      ((localFiberCoordinate P.good P.convex P.center_mem ha).comp (h.timeMap a))
      ((localFiberCoordinate P.good P.convex P.center_mem hb).comp (h.timeMap b)) := by
  let τ : C(CurveTime, CurveTime) :=
    ⟨fun r => ⟨AffineMap.lineMap a.val b.val r.val,
        (convex_Icc (0 : ℝ) 1).lineMap_mem a.property b.property r.property⟩,
      (by fun_prop)⟩
  let Γ : C(CurveTime × LaurentFiber f s, laurentTubeOpen f P.domain) :=
    ⟨fun q => ⟨h.curve q.2 (τ q.1),
        ((h.curve_spec q.2).2 (τ q.1) (τ q.1).property).1.1, by
          change laurentEval f (h.curve q.2 (τ q.1)) ∈ P.domain
          rw [((h.curve_spec q.2).2 (τ q.1) (τ q.1).property).2.2]
          exact hp q.1⟩,
      (h.curves_continuous.comp (continuous_snd.prodMk (τ.continuous.comp continuous_fst))).subtype_mk _⟩
  refine
    { toFun := fun q => tubeReferenceMap P.good P.convex P.center_mem (Γ q)
      continuous_toFun := (tubeReferenceMap P.good P.convex P.center_mem).continuous.comp Γ.continuous
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro z
    apply congrArg (tubeReferenceMap P.good P.convex P.center_mem)
    apply Subtype.ext
    change h.curve z (AffineMap.lineMap a.val b.val 0) = h.curve z a.val
    simp
  · intro z
    apply congrArg (tubeReferenceMap P.good P.convex P.center_mem)
    apply Subtype.ext
    change h.curve z (AffineMap.lineMap a.val b.val 1) = h.curve z b.val
    simp

theorem timeHomologyMap_coordinate_eq (h : LaurentC1Path f s t) (n : ℕ)
    (P : LaurentHomologyPatch f) (a b : CurveTime)
    (ha : h.base a ∈ P.domain) (hb : h.base b ∈ P.domain)
    (hp : ∀ r : CurveTime, h.base (AffineMap.lineMap a.val b.val r.val) ∈ P.domain) :
    h.timeHomologyMap n a ≫ (localFiberHomologyIso n P.good P.convex P.center_mem ha).hom =
      h.timeHomologyMap n b ≫ (localFiberHomologyIso n P.good P.convex P.center_mem hb).hom := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have H := h.timeCoordinateHomotopy P a b ha hb hp
  have H' : TopCat.Homotopy
      (TopCat.ofHom (h.timeMap a) ≫ TopCat.ofHom (localFiberCoordinate P.good P.convex P.center_mem ha))
      (TopCat.ofHom (h.timeMap b) ≫ TopCat.ofHom (localFiberCoordinate P.good P.convex P.center_mem hb)) := H
  change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
  rw [← F.map_comp, ← F.map_comp]
  exact H'.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n
/-- The prescribed path as a continuous map into the full good-value locus. -/
def baseGoodMap (h : LaurentC1Path f s t) : C(CurveTime, laurentGoodBaseSpace f) :=
  ⟨fun u => ⟨h.base u, h.good u u.property⟩, by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp
      (fun u hu => (h.base_deriv u hu).continuousWithinAt)⟩

/-- Near any time, interpolation with that time stays inside a single
convex good patch. The path itself need not lie in one global chart. -/
theorem exists_time_patch (h : LaurentC1Path f s t) (a : CurveTime) :
    ∃ (P : LaurentHomologyPatch f) (ε : ℝ), 0 < ε ∧ h.base a ∈ P.domain ∧
      ∀ b : CurveTime, dist b a < ε →
        ∀ r : CurveTime, h.base (AffineMap.lineMap a.val b.val r.val) ∈ P.domain := by
  obtain ⟨P, ha⟩ := laurentHomologyPatch_cover f (h.baseGoodMap a)
  have hopen := P.baseOpen.isOpen.preimage h.baseGoodMap.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a ha
  refine ⟨P, ε, hε, ha, ?_⟩
  intro b hb r
  let u : CurveTime := ⟨AffineMap.lineMap a.val b.val r.val,
    (convex_Icc (0 : ℝ) 1).lineMap_mem a.property b.property r.property⟩
  apply hball (a := u)
  change dist (AffineMap.lineMap a.val b.val r.val) a.val < ε
  exact (convex_ball a.val ε).lineMap_mem (Metric.mem_ball_self hε) hb r.property

end LaurentC1Path
end
end DuistermaatVanDerKallen
