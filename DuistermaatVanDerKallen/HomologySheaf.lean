import DuistermaatVanDerKallen.HomologyTransitions
import DuistermaatVanDerKallen.ConstantTransitionModuleSheaf

/-! The sheaf and covering space of the actual fiber homology sets over the
good-value locus. Coordinate changes come from the normalized-gradient maps. -/

open Set CategoryTheory AlgebraicTopology TopologicalSpace
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- The actual good-value locus, with its inherited topology. -/
def laurentGoodBaseSpace {d : ℕ} (f : MultiLaurent d) : TopCat :=
  TopCat.of (laurentGoodValues f)

/-- A convex open good neighborhood with a specified reference fiber. -/
structure LaurentHomologyPatch {d : ℕ} (f : MultiLaurent d) where
  domain : Opens ℂ
  good : GoodBase f domain
  convex : Convex ℝ (domain : Set ℂ)
  center : ℂ
  center_mem : center ∈ domain

namespace LaurentHomologyPatch
variable {d : ℕ} {f : MultiLaurent d}

def baseOpen (P : LaurentHomologyPatch f) : Opens (laurentGoodBaseSpace f) :=
  ⟨Subtype.val ⁻¹' (P.domain : Set ℂ), P.domain.isOpen.preimage continuous_subtype_val⟩

/-- Viewing a good neighborhood inside the good-value locus changes neither
its points nor its topology. -/
def baseHomeomorph (P : LaurentHomologyPatch f) : P.baseOpen ≃ₜ P.domain where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, P.good x.val x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem preconnected (P : LaurentHomologyPatch f) : PreconnectedSpace P.baseOpen := by
  let : PreconnectedSpace P.domain := isPreconnected_iff_preconnectedSpace.mp P.convex.isPreconnected
  exact P.baseHomeomorph.symm.surjective.denseRange.preconnectedSpace P.baseHomeomorph.symm.continuous

end LaurentHomologyPatch

/-- The good neighborhoods cover every actual good value. -/
theorem laurentHomologyPatch_cover {d : ℕ} (f : MultiLaurent d) (x : laurentGoodBaseSpace f) :
    ∃ P : LaurentHomologyPatch f, x ∈ P.baseOpen := by
  obtain ⟨D, hx, hD, hc, _, _⟩ := laurent_local_trivialization_at f x.property
  exact ⟨⟨D, hD, hc, x.val, hx⟩, hx⟩

/-- Actual integral homology groups as the fibers of a constant-transition
atlas. The transition identities are proved from ODE transport homotopies. -/
def laurentHomologyAtlas {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    ConstantTransitionAtlas (laurentGoodBaseSpace f) (fun x => laurentFiberHomology f x.val n) where
  Index := LaurentHomologyPatch f
  domain P := P.baseOpen
  model P := laurentFiberHomology f P.center n
  coord P x := (localFiberHomologyIso n P.good P.convex P.center_mem x.property).toLinearEquiv.toEquiv
  cover := laurentHomologyPatch_cover f
  transition P Q x y hxP hxQ hyP hyQ v := by
    have he := localHomologyTransition_eq_on_overlap n P.good P.convex P.center_mem hxP hyP
      Q.good Q.convex Q.center_mem hxQ hyQ
    exact congrArg (fun g : laurentFiberHomology f P.center n ⟶ laurentFiberHomology f Q.center n => g v) he

/-- A genuine sheaf of homology-valued locally constant coordinate sections.
This underlying set sheaf is refined to a sheaf of integral modules below. -/
def laurentHomologySheaf {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    TopCat.Sheaf (Type _) (laurentGoodBaseSpace f) := (laurentHomologyAtlas f n).sheaf

/-- Its actual sheaf stalk at a good value is the actual fiber homology set. -/
def laurentHomologyStalkEquiv {d : ℕ} (f : MultiLaurent d) (n : ℕ) (x : laurentGoodBaseSpace f) :
    (laurentHomologySheaf f n).presheaf.stalk x ≃ laurentFiberHomology f x.val n :=
  (laurentHomologyAtlas f n).stalkEquiv x

/-- Every chart gives unique extension of each germ across that whole chart. -/
theorem laurentHomologySheaf_germ_bijective {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    (P : LaurentHomologyPatch f) (x : laurentGoodBaseSpace f) (hx : x ∈ P.baseOpen) :
    Function.Bijective ((laurentHomologySheaf f n).presheaf.germ P.baseOpen x hx) := by
  let : PreconnectedSpace ((laurentHomologyAtlas f n).domain P) := P.preconnected
  exact (laurentHomologyAtlas f n).germ_bijective P x hx

/-- The étalé space is an actual covering space over the good-value locus,
with its fibers identified with the underlying integral homology sets. -/
theorem laurentHomologySheaf_isCoveringMap {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := (laurentHomologySheaf f n).presheaf)) :=
  (laurentHomologyAtlas f n).isCoveringMap_etale (fun P => P.preconnected)

/-- The same atlas with the full integral homology module structure. -/
def laurentHomologyModuleAtlas {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    ConstantTransitionModuleAtlas (laurentGoodBaseSpace f) (fun x => laurentFiberHomology f x.val n) where
  Index := LaurentHomologyPatch f
  domain P := P.baseOpen
  model P := laurentFiberHomology f P.center n
  coord P x := (localFiberHomologyIso n P.good P.convex P.center_mem x.property).toLinearEquiv
  cover := laurentHomologyPatch_cover f
  transition P Q x y hxP hxQ hyP hyQ v := by
    have he := localHomologyTransition_eq_on_overlap n P.good P.convex P.center_mem hxP hyP
      Q.good Q.convex Q.center_mem hxQ hyQ
    exact congrArg (fun g : laurentFiberHomology f P.center n ⟶ laurentFiberHomology f Q.center n => g v) he

theorem laurentHomologyModuleAtlas_toAtlas {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    (laurentHomologyModuleAtlas f n).toAtlas = laurentHomologyAtlas f n := rfl

/-- The global sheaf of integral homology modules on the actual good locus.
Its local constancy is expressed by the linear germ isomorphisms on the
covering convex patches below. -/
def laurentHomologyModuleSheaf {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    TopCat.Sheaf (ModuleCat ℤ) (laurentGoodBaseSpace f) :=
  (laurentHomologyModuleAtlas f n).sheaf

/-- The underlying section sheaf is exactly the one whose étalé space was
proved to be a covering. -/
theorem laurentHomologyModuleSheaf_forget {d : ℕ} (f : MultiLaurent d) (n : ℕ) :
    (laurentHomologyModuleSheaf f n).presheaf ⋙ forget (ModuleCat ℤ) =
      (laurentHomologySheaf f n).presheaf := rfl

/-- The actual module stalk is linearly identified with the actual integral
singular homology of the fiber. -/
def laurentHomologyStalkLinearEquiv {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    (x : laurentGoodBaseSpace f) :
    (laurentHomologyModuleSheaf f n).presheaf.stalk x ≃ₗ[ℤ] laurentFiberHomology f x.val n :=
  (laurentHomologyModuleAtlas f n).stalkLinearEquiv x

/-- Local constancy on every patch of the covering atlas: the germ map
from sections over the whole patch is a linear isomorphism at every point. -/
def laurentHomologyGermLinearEquiv {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    (P : LaurentHomologyPatch f) (x : laurentGoodBaseSpace f) (hx : x ∈ P.baseOpen) :
    (laurentHomologyModuleSheaf f n).presheaf.obj (Opposite.op P.baseOpen) ≃ₗ[ℤ]
      (laurentHomologyModuleSheaf f n).presheaf.stalk x := by
  let : PreconnectedSpace ((laurentHomologyModuleAtlas f n).domain P) := P.preconnected
  exact (laurentHomologyModuleAtlas f n).germLinearEquiv P x hx

/-- A section of the global homology sheaf is transported by the actual
normalized-gradient ODE map along every C¹ path inside one coordinate patch. -/
theorem laurentHomologySection_transport {d : ℕ} {f : MultiLaurent d} {s t : ℂ}
    (h : LaurentC1Path f s t) (n : ℕ) (P : LaurentHomologyPatch f)
    (hs : s ∈ P.domain) (ht : t ∈ P.domain)
    (hp : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ P.domain)
    (σ : (laurentHomologyModuleAtlas f n).sections P.baseOpen) :
    h.homologyMap n (σ.val ⟨⟨s, P.good s hs⟩, hs⟩) =
      σ.val ⟨⟨t, P.good t ht⟩, ht⟩ := by
  let A := laurentHomologyModuleAtlas f n
  let : PreconnectedSpace P.baseOpen := P.preconnected
  let : PreconnectedSpace (A.toAtlas.domain P) := P.preconnected
  have he := A.toAtlas.coordinate_locallyConstant σ.val σ.property P le_rfl
  have he' := he.apply_eq_of_preconnectedSpace
    ⟨⟨s, P.good s hs⟩, hs⟩ ⟨⟨t, P.good t ht⟩, ht⟩
  apply (localFiberHomologyIso n P.good P.convex P.center_mem ht).toLinearEquiv.injective
  have hm := congrArg
    (fun k : laurentFiberHomology f s n ⟶ laurentFiberHomology f P.center n =>
      k (σ.val ⟨⟨s, P.good s hs⟩, hs⟩))
    (h.homologyMap_comp_coordinate n P.good P.convex P.center_mem hs ht hp)
  exact hm.trans he'

end
end DuistermaatVanDerKallen
