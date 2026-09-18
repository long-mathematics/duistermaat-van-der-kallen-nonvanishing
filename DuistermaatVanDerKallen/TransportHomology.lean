import DuistermaatVanDerKallen.LocalTransportHomotopy
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! Singular homology maps induced by the actual complete fiber transport,
and their agreement with local trivializations in a convex good neighborhood. -/

open CategoryTheory AlgebraicTopology
open Set
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- Integral singular homology of the actual Laurent fiber, in any degree. -/
abbrev laurentFiberHomology {d : ℕ} (f : MultiLaurent d) (s : ℂ) (n : ℕ) :=
  (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (LaurentFiber f s)))

namespace LaurentC1Path
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

/-- The homology map induced by the complete normalized-gradient transport. -/
def homologyMap (h : LaurentC1Path f s t) (n : ℕ) :
    laurentFiberHomology f s n ⟶ laurentFiberHomology f t n :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom h.transportMap)

/-- Complete path transport induces an isomorphism on integral singular
homology; its inverse is induced by the reversed path. -/
def homologyIso (h : LaurentC1Path f s t) (n : ℕ) :
    laurentFiberHomology f s n ≅ laurentFiberHomology f t n :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo
      { toEquiv := h.transportEquiv
        continuous_toFun := h.transport_continuous
        continuous_invFun := h.reverse.transport_continuous })

@[simp] theorem homologyIso_hom (h : LaurentC1Path f s t) (n : ℕ) :
    (h.homologyIso n).hom = h.homologyMap n := rfl

@[simp] theorem homologyIso_inv (h : LaurentC1Path f s t) (n : ℕ) :
    (h.homologyIso n).inv = h.reverse.homologyMap n := rfl

/-- The homology class is constant in any fixed local-trivialization
coordinate along a path contained in that convex good neighborhood. -/
theorem homologyMap_comp_coordinate (h : LaurentC1Path f s t) (n : ℕ)
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hb : b ∈ D) (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D) :
    h.homologyMap n ≫
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (localFiberCoordinate hD hc hb ht)) =
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (localFiberCoordinate hD hc hb hs)) := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have H : TopCat.Homotopy (TopCat.ofHom (localFiberCoordinate hD hc hb hs))
      (TopCat.ofHom h.transportMap ≫ TopCat.ofHom (localFiberCoordinate hD hc hb ht)) :=
    h.localCoordinateHomotopy hD hc hb hs ht hpath
  change F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  exact (H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n).symm

/-- Within one convex good neighborhood, the actual C¹ transport and local
product identification induce the same integral singular-homology map. -/
theorem homologyMap_eq_local (h : LaurentC1Path f s t) (n : ℕ)
    {D : TopologicalSpace.Opens ℂ} (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D) :
    h.homologyMap n =
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (localFiberCoordinate hD hc ht hs)) := by
  have H : TopCat.Homotopy (TopCat.ofHom (localFiberCoordinate hD hc ht hs))
      (TopCat.ofHom h.transportMap) := h.localTransportHomotopy hD hc hs ht hpath
  exact (H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n).symm

/-- Convex-local path independence on homology; this is not invariance under
arbitrary loops in the full good-value locus. -/
theorem homologyMap_eq_of_convex (h k : LaurentC1Path f s t) (n : ℕ)
    {D : TopologicalSpace.Opens ℂ} (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D)
    (kpath : ∀ r ∈ Icc (0 : ℝ) 1, k.base r ∈ D) :
    h.homologyMap n = k.homologyMap n :=
  (h.homologyMap_eq_local n hD hc hs ht hpath).trans
    (k.homologyMap_eq_local n hD hc hs ht kpath).symm

end LaurentC1Path

namespace LaurentC1Chain
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

def transportMap (h : LaurentC1Chain f s t) : C(LaurentFiber f s, LaurentFiber f t) :=
  ⟨h.transport, h.transport_continuous⟩

/-- The map of integral homology induced by a finite chain of C¹ pieces. -/
def homologyMap (h : LaurentC1Chain f s t) (n : ℕ) :
    laurentFiberHomology f s n ⟶ laurentFiberHomology f t n :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom h.transportMap)

def homologyIso (h : LaurentC1Chain f s t) (n : ℕ) :
    laurentFiberHomology f s n ≅ laurentFiberHomology f t n :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo
      { toEquiv := h.transportEquiv
        continuous_toFun := h.transport_continuous
        continuous_invFun := h.transportBack_continuous })

@[simp] theorem homologyIso_hom (h : LaurentC1Chain f s t) (n : ℕ) :
    (h.homologyIso n).hom = h.homologyMap n := rfl

@[simp] theorem homologyMap_single (h : LaurentC1Path f s t) (n : ℕ) :
    (single h).homologyMap n = h.homologyMap n := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have he : TopCat.ofHom (single h).transportMap = TopCat.ofHom h.transportMap := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change (single h).transport z = h.transport z
    simp only [transport]
  exact congrArg F.map he

/-- Composition of the actual trajectory pieces gives composition of the
induced homology maps in the same order. -/
theorem homologyMap_append {u : ℂ} (h : LaurentC1Chain f s t) (k : LaurentC1Path f t u) (n : ℕ) :
    (h.append k).homologyMap n = h.homologyMap n ≫ k.homologyMap n := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have he : TopCat.ofHom (h.append k).transportMap =
      TopCat.ofHom h.transportMap ≫ TopCat.ofHom k.transportMap := by
    ext z
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_ofHom,
      transportMap, ContinuousMap.coe_mk, transport, Function.comp_apply, LaurentC1Path.transportMap]
  change F.map _ = F.map _ ≫ F.map _
  rw [he, F.map_comp]

/-- The same local-coordinate constancy holds for a finite chain, including
its corners, by composing the homology identities of its individual pieces. -/
theorem homologyMap_comp_coordinate (h : LaurentC1Chain f s t) (n : ℕ)
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hb : b ∈ D) (hs : s ∈ D) (ht : t ∈ D) (hpath : h.StaysIn D) :
    h.homologyMap n ≫
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (localFiberCoordinate hD hc hb ht)) =
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (localFiberCoordinate hD hc hb hs)) := by
  revert hs ht hpath
  induction h with
  | single h =>
    intro hs ht hpath
    simp only [StaysIn, SetLike.mem_coe] at hpath
    rw [homologyMap_single]
    exact h.homologyMap_comp_coordinate n hD hc hb hs ht hpath
  | append h k ih =>
    intro hs ht hpath
    simp only [StaysIn, SetLike.mem_coe] at hpath
    have hk : ∀ r ∈ Icc (0 : ℝ) 1, k.base r ∈ D := hpath.2
    have hmid := hk 0 (by simp)
    rw [k.base_zero] at hmid
    rw [homologyMap_append, Category.assoc,
      k.homologyMap_comp_coordinate n hD hc hb hmid ht hk]
    exact ih hs hmid hpath.1

end LaurentC1Chain
end
end DuistermaatVanDerKallen
