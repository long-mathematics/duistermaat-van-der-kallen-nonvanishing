import DuistermaatVanDerKallen.C1Sweeps
import DuistermaatVanDerKallen.LocalTrivialization
import Mathlib.Topology.Homotopy.Basic

/-! Within a convex good base, the complete C¹ endpoint map is homotopic to
its local-trivialization identification. Arbitrary loops are not discarded. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- The continuous fiber coordinate of the manuscript's local product map. -/
def tubeReferenceMap {d : ℕ} {f : MultiLaurent d}
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D) :
    C(laurentTubeOpen f D, LaurentFiber f b) := by
  let : Fact (RegularLaurentValue f b) := ⟨hD.regularValue hb⟩
  exact ⟨fun y => (convexTransportBack hD hc hb y).2,
    (convexTransportBack_contMDiff hD hc hb).continuous.snd⟩

/-- The inclusion of an individual fiber into a tube over an open base. -/
def fiberToTube {d : ℕ} (f : MultiLaurent d) (D : TopologicalSpace.Opens ℂ)
    {s : ℂ} (hs : s ∈ D) : C(LaurentFiber f s, laurentTubeOpen f D) :=
  ⟨fun z => ⟨z.val, z.property.1, by
    change laurentEval f z.val ∈ D
    rw [z.property.2]
    exact hs⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The local-trivialization identification with its reference fiber. -/
def localFiberCoordinate {d : ℕ} {f : MultiLaurent d}
    {D : TopologicalSpace.Opens ℂ} {b s : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D) (hs : s ∈ D) :
    C(LaurentFiber f s, LaurentFiber f b) :=
  (tubeReferenceMap hD hc hb).comp (fiberToTube f D hs)

/-- At the reference fiber the local identification is the identity. -/
theorem localFiberCoordinate_center {d : ℕ} {f : MultiLaurent d}
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D)
    (z : LaurentFiber f b) : localFiberCoordinate hD hc hb hb z = z := by
  apply Subtype.ext
  have hp := convexTransportBack_admissible hD hc hb (fiberToTube f D hb z)
  have hp' : (0, z.val) ∈ admissibleSegmentParameters f := by
    simpa only [fiberToTube, ContinuousMap.coe_mk, z.property.2, sub_self] using hp
  change laurentSegmentCurve f (b - laurentEval f z.val, z.val) 1 = z.val
  rw [z.property.2, sub_self]
  exact (laurentSegmentCurve_eq_fiberCurve hp'.2 ⟨z.val, hp'.1, rfl⟩ (by simp)).trans
    (fiberTransport_zero hp'.2 ⟨z.val, hp'.1, rfl⟩)

namespace LaurentC1Path
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

/-- Bundled complete endpoint transport, retaining the original fiber topology. -/
def transportMap (h : LaurentC1Path f s t) : C(LaurentFiber f s, LaurentFiber f t) :=
  ⟨h.transport, h.transport_continuous⟩

/-- The complete trajectory, now as a jointly continuous map into a chosen tube. -/
def tubeCurve (h : LaurentC1Path f s t) (D : TopologicalSpace.Opens ℂ)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D) :
    C(CurveTime × LaurentFiber f s, laurentTubeOpen f D) :=
  ⟨fun p => ⟨h.curve p.2 p.1, ((h.curve_spec p.2).2 p.1 p.1.property).1.1,
    by rw [((h.curve_spec p.2).2 p.1 p.1.property).2.2]; exact hpath p.1 p.1.property⟩,
    (h.curves_continuous.comp continuous_swap).subtype_mk _⟩

/-- In any reference-fiber coordinate, the transported family is a homotopy
from the initial identification to the terminal identification after transport. -/
def localCoordinateHomotopy (h : LaurentC1Path f s t)
    {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hb : b ∈ D) (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D) :
    ContinuousMap.Homotopy (localFiberCoordinate hD hc hb hs)
      ((localFiberCoordinate hD hc hb ht).comp h.transportMap) where
  toFun p := tubeReferenceMap hD hc hb (h.tubeCurve D hpath p)
  continuous_toFun := (tubeReferenceMap hD hc hb).continuous.comp (h.tubeCurve D hpath).continuous
  map_zero_left z := by
    apply congrArg (tubeReferenceMap hD hc hb)
    apply Subtype.ext
    exact (h.curve_spec z).1
  map_one_left z := by
    apply congrArg (tubeReferenceMap hD hc hb)
    apply Subtype.ext
    rfl

/-- Compare the actual driven transport with the local product identification
by projecting the whole trajectory to the terminal reference fiber. -/
def localTransportHomotopy (h : LaurentC1Path f s t)
    {D : TopologicalSpace.Opens ℂ} (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D) :
    ContinuousMap.Homotopy (localFiberCoordinate hD hc ht hs) h.transportMap where
  toFun p := tubeReferenceMap hD hc ht (h.tubeCurve D hpath p)
  continuous_toFun := (tubeReferenceMap hD hc ht).continuous.comp (h.tubeCurve D hpath).continuous
  map_zero_left z := by
    apply congrArg (tubeReferenceMap hD hc ht)
    apply Subtype.ext
    exact (h.curve_spec z).1
  map_one_left z := by
    change tubeReferenceMap hD hc ht (h.tubeCurve D hpath (1, z)) = h.transport z
    have he : h.tubeCurve D hpath (1, z) = fiberToTube f D ht (h.transport z) := by
      apply Subtype.ext
      rfl
    rw [he]
    exact localFiberCoordinate_center hD hc ht (h.transport z)

/-- Any two C¹ paths with the same endpoints inside one convex good base
induce homotopic fiber maps. No assertion about arbitrary loops is made. -/
def transportHomotopyOfConvex (h k : LaurentC1Path f s t)
    {D : TopologicalSpace.Opens ℂ} (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D)
    (kpath : ∀ r ∈ Icc (0 : ℝ) 1, k.base r ∈ D) :
    ContinuousMap.Homotopy h.transportMap k.transportMap :=
  (h.localTransportHomotopy hD hc hs ht hpath).symm.trans
    (k.localTransportHomotopy hD hc hs ht kpath)

end LaurentC1Path
end
end DuistermaatVanDerKallen
