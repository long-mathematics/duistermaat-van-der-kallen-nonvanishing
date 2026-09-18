import DuistermaatVanDerKallen.TransportHomology

/-! Local homology coordinates and constant transition maps on convex overlaps. -/

open Set CategoryTheory AlgebraicTopology
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

def localFiberHomologyIso {d : ℕ} {f : MultiLaurent d} (n : ℕ)
    {D : TopologicalSpace.Opens ℂ} {b s : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D) (hs : s ∈ D) :
    laurentFiberHomology f s n ≅ laurentFiberHomology f b n :=
  ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo (localFiberCoordinateHomeomorph hD hc hb hs))

theorem LaurentC1Path.homologyMap_eq_coordinate_iso {d : ℕ} {f : MultiLaurent d} {s t : ℂ}
    (h : LaurentC1Path f s t) (n : ℕ) {D : TopologicalSpace.Opens ℂ} {b : ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ))
    (hb : b ∈ D) (hs : s ∈ D) (ht : t ∈ D)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D) :
    h.homologyMap n = (localFiberHomologyIso n hD hc hb hs).hom ≫
      (localFiberHomologyIso n hD hc hb ht).inv := by
  symm
  apply ((localFiberHomologyIso n hD hc hb ht).comp_inv_eq).mpr
  exact (h.homologyMap_comp_coordinate n hD hc hb hs ht hpath).symm

/-- Coordinate-change maps agree at the ends of a path lying in the overlap. -/
theorem localHomologyTransition_eq_along_path {d : ℕ} {f : MultiLaurent d} {s t : ℂ}
    (h : LaurentC1Path f s t) (n : ℕ)
    {D E : TopologicalSpace.Opens ℂ} {a b : ℂ}
    (hD : GoodBase f D) (hcD : Convex ℝ (D : Set ℂ)) (ha : a ∈ D)
    (hsD : s ∈ D) (htD : t ∈ D) (hpD : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ D)
    (hE : GoodBase f E) (hcE : Convex ℝ (E : Set ℂ)) (hb : b ∈ E)
    (hsE : s ∈ E) (htE : t ∈ E) (hpE : ∀ r ∈ Icc (0 : ℝ) 1, h.base r ∈ E) :
    (localFiberHomologyIso n hD hcD ha hsD).inv ≫ (localFiberHomologyIso n hE hcE hb hsE).hom =
      (localFiberHomologyIso n hD hcD ha htD).inv ≫ (localFiberHomologyIso n hE hcE hb htE).hom := by
  let AS := localFiberHomologyIso n hD hcD ha hsD
  let AT := localFiberHomologyIso n hD hcD ha htD
  let BS := localFiberHomologyIso n hE hcE hb hsE
  let BT := localFiberHomologyIso n hE hcE hb htE
  have hA : h.homologyMap n ≫ AT.hom = AS.hom :=
    h.homologyMap_comp_coordinate n hD hcD ha hsD htD hpD
  have hB : h.homologyMap n ≫ BT.hom = BS.hom :=
    h.homologyMap_comp_coordinate n hE hcE hb hsE htE hpE
  change AS.inv ≫ BS.hom = AT.inv ≫ BT.hom
  apply (cancel_epi AS.hom).mp
  calc
    AS.hom ≫ (AS.inv ≫ BS.hom) = BS.hom := by simp
    _ = h.homologyMap n ≫ BT.hom := hB.symm
    _ = AS.hom ≫ (AT.inv ≫ BT.hom) := by rw [← hA]; simp

/-- The homology transition between two convex charts is constant on their overlap. -/
theorem localHomologyTransition_eq_on_overlap {d : ℕ} {f : MultiLaurent d} {s t : ℂ} (n : ℕ)
    {D E : TopologicalSpace.Opens ℂ} {a b : ℂ}
    (hD : GoodBase f D) (hcD : Convex ℝ (D : Set ℂ)) (ha : a ∈ D)
    (hsD : s ∈ D) (htD : t ∈ D)
    (hE : GoodBase f E) (hcE : Convex ℝ (E : Set ℂ)) (hb : b ∈ E)
    (hsE : s ∈ E) (htE : t ∈ E) :
    (localFiberHomologyIso n hD hcD ha hsD).inv ≫ (localFiberHomologyIso n hE hcE hb hsE).hom =
      (localFiberHomologyIso n hD hcD ha htD).inv ≫ (localFiberHomologyIso n hE hcE hb htE).hom := by
  let hseg := hD.segment hcD hsD htD
  exact localHomologyTransition_eq_along_path (LaurentC1Path.line hseg) n hD hcD ha hsD htD
    (fun r hr => LaurentC1Path.line_base_mem hseg hcD hsD htD hr)
    hE hcE hb hsE htE (fun r hr => LaurentC1Path.line_base_mem hseg hcE hsE htE hr)

end
end DuistermaatVanDerKallen
