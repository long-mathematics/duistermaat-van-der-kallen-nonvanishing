import DuistermaatVanDerKallen.TimeHomology
import Mathlib.Topology.Homotopy.Lifting

/-! The complete ODE homology class is a continuous path in the étalé
covering of the global integral homology sheaf. -/

open Set CategoryTheory AlgebraicTopology TopologicalSpace Filter
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

abbrev LaurentHomologyEtale {d : ℕ} (f : MultiLaurent d) (n : ℕ) :=
  (laurentHomologyModuleSheaf f n).presheaf.EtaleSpace

theorem laurentHomologyModuleSheaf_isCoveringMap {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := (laurentHomologyModuleSheaf f n).presheaf)) :=
  (laurentHomologyModuleAtlas f n).isCoveringMap_module_etale (fun P => P.preconnected)

/-- A fiber homology class as a point in the actual module-stalk covering. -/
def homologyEtalePoint {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    (x : laurentGoodBaseSpace f) (c : laurentFiberHomology f x.val n) : LaurentHomologyEtale f n :=
  ⟨x, (laurentHomologyStalkLinearEquiv f n x).symm c⟩

/-- Fiber identifications over equal base points preserve the corresponding
point of the stalk covering. -/
theorem homologyEtalePoint_map_eq {d : ℕ} (f : MultiLaurent d) (n : ℕ) (Y : TopCat)
    {x y : laurentGoodBaseSpace f} (hxy : x = y)
    (g : C(Y, LaurentFiber f x.val)) (k : C(Y, LaurentFiber f y.val))
    (hgk : ∀ z, (g z).val = (k z).val)
    (c : ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj Y) :
    homologyEtalePoint f n x
      (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g) c) =
    homologyEtalePoint f n y
      (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom k) c) := by
  subst y
  have he : g = k := ContinuousMap.ext (fun z => Subtype.ext (hgk z))
  subst k
  rfl

theorem homologyEtalePoint_injective {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    (x : laurentGoodBaseSpace f) : Function.Injective (homologyEtalePoint f n x) := by
  intro c d he
  have hg : (laurentHomologyStalkLinearEquiv f n x).symm c =
      (laurentHomologyStalkLinearEquiv f n x).symm d := by
    injection he
  exact (laurentHomologyStalkLinearEquiv f n x).symm.injective hg

namespace LaurentC1Path
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

/-- The class obtained by the actual partial trajectory, in its sheaf stalk. -/
def homologyLift (h : LaurentC1Path f s t) (n : ℕ) (c : laurentFiberHomology f s n)
    (u : CurveTime) : LaurentHomologyEtale f n :=
  homologyEtalePoint f n (h.baseGoodMap u) (h.timeHomologyMap n u c)

/-- Near any time, the lifted class is the germ of one fixed chart section. -/
theorem homologyLift_locally_section (h : LaurentC1Path f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) (a : CurveTime) :
    ∃ (P : LaurentHomologyPatch f) (ε : ℝ), 0 < ε ∧
      ∃ (σ : (laurentHomologyModuleAtlas f n).sections P.baseOpen),
        ∀ b : CurveTime, dist b a < ε → ∃ hb : h.baseGoodMap b ∈ P.baseOpen,
          h.homologyLift n c b =
            (laurentHomologyModuleAtlas f n).sectionEtaleMap P.baseOpen σ ⟨h.baseGoodMap b, hb⟩ := by
  let A := laurentHomologyModuleAtlas f n
  obtain ⟨P, ε, hε, ha, hp⟩ := h.exists_time_patch a
  let v := (localFiberHomologyIso n P.good P.convex P.center_mem ha).hom
    (h.timeHomologyMap n a c)
  let σ : A.sections P.baseOpen :=
    ⟨A.toAtlas.constantSection P v, A.toAtlas.constantSection_local P v⟩
  refine ⟨P, ε, hε, σ, ?_⟩
  intro b hb
  have hbP : h.base b ∈ P.domain := by simpa using hp b hb (1 : CurveTime)
  refine ⟨hbP, ?_⟩
  change TopCat.Presheaf.EtaleSpace.mk (h.baseGoodMap b) _ =
    TopCat.Presheaf.EtaleSpace.mk (h.baseGoodMap b) _
  congr 1
  apply (A.stalkLinearEquiv (h.baseGoodMap b)).injective
  have hleft : A.stalkLinearEquiv (h.baseGoodMap b)
      ((laurentHomologyStalkLinearEquiv f n (h.baseGoodMap b)).symm (h.timeHomologyMap n b c)) =
      h.timeHomologyMap n b c := (A.stalkLinearEquiv _).apply_symm_apply _
  rw [hleft]
  change h.timeHomologyMap n b c = A.stalkEval (h.baseGoodMap b)
    (A.presheaf.germ P.baseOpen (h.baseGoodMap b) hbP σ)
  apply Eq.trans ?_ (A.stalkEval_germ P.baseOpen (h.baseGoodMap b) hbP σ).symm
  apply (localFiberHomologyIso n P.good P.convex P.center_mem hbP).toLinearEquiv.injective
  have hcoord := congrArg
    (fun k : laurentFiberHomology f s n ⟶ laurentFiberHomology f P.center n => k c)
    (h.timeHomologyMap_coordinate_eq n P a b ha hbP (hp b hb))
  exact hcoord.symm.trans ((A.coord P ⟨h.baseGoodMap b, hbP⟩).apply_symm_apply v).symm

/-- The actual ODE homology class gives a continuous lift in the covering. -/
theorem homologyLift_continuous (h : LaurentC1Path f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) : Continuous (h.homologyLift n c) := by
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨P, ε, hε, σ, he⟩ := h.homologyLift_locally_section n c a
  let A := laurentHomologyModuleAtlas f n
  let : PreconnectedSpace (A.domain P) := P.preconnected
  have hcont : ContinuousOn (h.homologyLift n c) (Metric.ball a ε) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let β : C(Metric.ball a ε, P.baseOpen) :=
      ⟨fun b => ⟨h.baseGoodMap b.val, (he b.val b.property).choose⟩,
        (h.baseGoodMap.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hc := (A.sectionEtaleMap_continuous P σ).comp β.continuous
    apply hc.congr
    intro b
    exact (he b.val b.property).choose_spec.symm
  exact hcont.continuousAt (Metric.ball_mem_nhds a hε)

/-- The starting good value, with the path's verified exclusion proof. -/
def sourceGood (h : LaurentC1Path f s t) : laurentGoodBaseSpace f :=
  ⟨s, by
    have hs : h.base 0 ∈ laurentGoodValues f := h.good 0 (by simp)
    exact h.base_zero ▸ hs⟩

/-- The terminal good value, with the path's verified exclusion proof. -/
def targetGood (h : LaurentC1Path f s t) : laurentGoodBaseSpace f :=
  ⟨t, by
    have ht : h.base 1 ∈ laurentGoodValues f := h.good 1 (by simp)
    exact h.base_one ▸ ht⟩

theorem homologyLift_zero (h : LaurentC1Path f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) :
    h.homologyLift n c 0 = homologyEtalePoint f n h.sourceGood c := by
  have he := homologyEtalePoint_map_eq f n (TopCat.of (LaurentFiber f s))
    (x := h.baseGoodMap 0) (y := h.sourceGood) (Subtype.ext h.base_zero)
    (h.timeMap 0) (ContinuousMap.id _) (fun z => (h.curve_spec z).1) c
  change h.homologyLift n c 0 = _ at he
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have hm := congrArg (fun m : laurentFiberHomology f s n ⟶ laurentFiberHomology f s n => m c)
    (F.map_id (TopCat.of (LaurentFiber f s)))
  exact he.trans (congrArg (homologyEtalePoint f n h.sourceGood) hm)

theorem homologyLift_one (h : LaurentC1Path f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) :
    h.homologyLift n c 1 = homologyEtalePoint f n h.targetGood (h.homologyMap n c) :=
  homologyEtalePoint_map_eq f n (TopCat.of (LaurentFiber f s))
    (x := h.baseGoodMap 1) (y := h.targetGood) (Subtype.ext h.base_one) (h.timeMap 1) h.transportMap (fun _ => rfl) c

/-- The path in the actual good-value locus, retaining the fixed endpoints. -/
def basePath (h : LaurentC1Path f s t) : Path h.sourceGood h.targetGood where
  toContinuousMap := h.baseGoodMap
  source' := Subtype.ext h.base_zero
  target' := Subtype.ext h.base_one

/-- The actual ODE homology class agrees with the unique covering-space lift. -/
theorem homologyLift_eq_liftPath (h : LaurentC1Path f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) :
    h.homologyLift n c =
      (laurentHomologyModuleSheaf_isCoveringMap f n).liftPath h.baseGoodMap
        (homologyEtalePoint f n h.sourceGood c) (Subtype.ext h.base_zero) := by
  apply (IsCoveringMap.eq_liftPath_iff _ _).mpr
  exact ⟨h.homologyLift_continuous n c, rfl, h.homologyLift_zero n c⟩

/-- General fixed-endpoint homotopy invariance of the actual normalized-gradient
homology maps. The homotopy may pass through arbitrarily many good charts. -/
theorem homologyMap_eq_of_homotopicRel (h k : LaurentC1Path f s t) (n : ℕ)
    (H : h.baseGoodMap.HomotopicRel k.baseGoodMap {0, 1}) :
    h.homologyMap n = k.homologyMap n := by
  ext c
  apply homologyEtalePoint_injective f n h.targetGood
  calc
    homologyEtalePoint f n h.targetGood (h.homologyMap n c) = h.homologyLift n c 1 :=
      (h.homologyLift_one n c).symm
    _ = k.homologyLift n c 1 := by
      rw [h.homologyLift_eq_liftPath, k.homologyLift_eq_liftPath]
      exact (laurentHomologyModuleSheaf_isCoveringMap f n).liftPath_apply_one_eq_of_homotopicRel
        H (homologyEtalePoint f n h.sourceGood c) _ _
    _ = homologyEtalePoint f n h.targetGood (k.homologyMap n c) := k.homologyLift_one n c

/-- The same theorem in the ordinary path-homotopy API. -/
theorem homologyMap_eq_of_homotopic (h k : LaurentC1Path f s t) (n : ℕ)
    (H : h.basePath.Homotopic k.basePath) : h.homologyMap n = k.homologyMap n :=
  h.homologyMap_eq_of_homotopicRel k n H

/-- The endpoint identification expressed in mathlib's monodromy API. -/
theorem monodromy_homologyMap (h : LaurentC1Path f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) :
    (laurentHomologyModuleSheaf_isCoveringMap f n).monodromy
      (Path.Homotopic.Quotient.mk h.basePath)
      ⟨homologyEtalePoint f n h.sourceGood c, rfl⟩ =
      ⟨homologyEtalePoint f n h.targetGood (h.homologyMap n c), rfl⟩ := by
  apply Subtype.ext
  exact (congr_fun (h.homologyLift_eq_liftPath n c) 1).symm.trans (h.homologyLift_one n c)

end LaurentC1Path
end
end DuistermaatVanDerKallen
