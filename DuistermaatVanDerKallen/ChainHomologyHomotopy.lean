import DuistermaatVanDerKallen.HomologyLift

/-! Comparison with covering-space transport and homotopy invariance for
finite endpoint-matching chains of C¹ pieces, including their corners. -/

open Set CategoryTheory TopologicalSpace
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section
namespace LaurentC1Chain
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

def sourceGood (h : LaurentC1Chain f s t) : laurentGoodBaseSpace f :=
  ⟨s, by
    induction h with
    | single h => exact h.sourceGood.property
    | append _ _ ih => exact ih⟩

def targetGood (h : LaurentC1Chain f s t) : laurentGoodBaseSpace f :=
  ⟨t, by
    cases h with
    | single h => exact h.targetGood.property
    | append _ h => exact h.targetGood.property⟩

/-- Concatenation of the continuous base paths of the individual pieces. -/
def basePath : {s t : ℂ} → (h : LaurentC1Chain f s t) → Path h.sourceGood h.targetGood
  | _, _, .single h => h.basePath
  | _, _, .append h k => h.basePath.trans k.basePath

/-- The actual finite composition of ODE homology maps is precisely
transport in the global covering along the concatenated base path. -/
theorem monodromy_homologyMap (h : LaurentC1Chain f s t) (n : ℕ)
    (c : laurentFiberHomology f s n) :
    (laurentHomologyModuleSheaf_isCoveringMap f n).monodromy
      (Path.Homotopic.Quotient.mk h.basePath)
      ⟨homologyEtalePoint f n h.sourceGood c, rfl⟩ =
      ⟨homologyEtalePoint f n h.targetGood (h.homologyMap n c), rfl⟩ := by
  induction h with
  | single h =>
    simpa only [basePath, sourceGood, targetGood, LaurentC1Path.sourceGood,
      LaurentC1Path.targetGood, homologyMap_single] using h.monodromy_homologyMap n c
  | @append t u h k ih =>
    simp only [basePath]
    let cov := laurentHomologyModuleSheaf_isCoveringMap f n
    change cov.monodromy (Path.Homotopic.Quotient.mk (h.basePath.trans k.basePath))
      ⟨homologyEtalePoint f n h.sourceGood c, rfl⟩ =
      ⟨homologyEtalePoint f n k.targetGood ((h.append k).homologyMap n c), rfl⟩
    apply (cov.monodromy_trans_apply (Path.Homotopic.Quotient.mk h.basePath)
      (Path.Homotopic.Quotient.mk k.basePath)
      ⟨homologyEtalePoint f n h.sourceGood c, rfl⟩).trans
    apply (congrArg (cov.monodromy (Path.Homotopic.Quotient.mk k.basePath)) ih).trans
    have hk := k.monodromy_homologyMap n (h.homologyMap n c)
    apply hk.trans
    apply Subtype.ext
    apply congrArg (homologyEtalePoint f n k.targetGood)
    exact (congrArg (fun m : laurentFiberHomology f s n ⟶ laurentFiberHomology f u n => m c)
      (h.homologyMap_append k n)).symm

/-- Arbitrary fixed-endpoint homotopies in the full good locus preserve the
actual homology map of a finite C¹ chain. No differentiability at corners or
smoothness of the homotopy is assumed. -/
theorem homologyMap_eq_of_homotopic (h k : LaurentC1Chain f s t) (n : ℕ)
    (H : h.basePath.Homotopic k.basePath) : h.homologyMap n = k.homologyMap n := by
  have hp : Path.Homotopic.Quotient.mk h.basePath = Path.Homotopic.Quotient.mk k.basePath :=
    Path.Homotopic.Quotient.eq.mpr H
  ext c
  apply homologyEtalePoint_injective f n h.targetGood
  have hh := h.monodromy_homologyMap n c
  have hk := k.monodromy_homologyMap n c
  rw [hp] at hh
  exact congrArg Subtype.val (hh.symm.trans hk)

/-- A loop acts trivially when it is null-homotopic in the good-value locus.
The null-homotopy is an explicit premise; arbitrary loops may have monodromy. -/
theorem homologyMap_eq_id_of_nullhomotopic (h : LaurentC1Chain f s s) (n : ℕ)
    (H : h.basePath.Homotopic (Path.refl h.sourceGood)) :
    h.homologyMap n = 𝟙 (laurentFiberHomology f s n) := by
  have hp : Path.Homotopic.Quotient.mk h.basePath = Path.Homotopic.Quotient.refl h.sourceGood :=
    Path.Homotopic.Quotient.eq.mpr H
  ext c
  apply homologyEtalePoint_injective f n h.sourceGood
  have hh := h.monodromy_homologyMap n c
  rw [hp] at hh
  have hr := congr_fun ((laurentHomologyModuleSheaf_isCoveringMap f n).monodromy_refl
    (x := h.sourceGood)) ⟨homologyEtalePoint f n h.sourceGood c, rfl⟩
  exact congrArg Subtype.val (hh.symm.trans hr)

end LaurentC1Chain
end
end DuistermaatVanDerKallen
