import DuistermaatVanDerKallen.LatticeCoordinates

/-! Real extensions of integral coordinate automorphisms preserve Newton interior. -/

open Set
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- Extend an integral linear map by its values on the standard basis. -/
def realExponentMap {d : ℕ} (E : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ)) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Fintype.linearCombination ℝ (fun i => exponentVector (E (Pi.single i 1)))

theorem realExponentMap_exponentVector {d : ℕ}
    (E : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ)) (a : Fin d → ℤ) :
    realExponentMap E (exponentVector a) = exponentVector (E a) := by
  have ha : (∑ i, a i • Pi.single i (1 : ℤ)) = a := by
    simpa using (Pi.basisFun ℤ (Fin d)).sum_repr a
  change (∑ i, (a i : ℝ) • exponentVector (E (Pi.single i 1))) = exponentLinearMap (E a)
  conv_rhs => rw [← ha, map_sum, map_sum]
  simp only [map_smul]
  congr 1
  ext i j
  simp [exponentLinearMap, exponentVector]

theorem realExponentMap_injective {d : ℕ}
    (E : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ)) (hE : Function.Injective E) :
    Function.Injective (realExponentMap E) := by
  have hi : LinearIndependent ℤ (fun i : Fin d => E (Pi.single i 1)) :=
    by simpa only [Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun ℤ (Fin d)).linearIndependent.map' E (LinearMap.ker_eq_bot.mpr hE)
  have hr : LinearIndependent ℝ (fun i : Fin d => exponentVector (E (Pi.single i 1))) :=
    linearIndependent_algebraMap_comp_iff.mpr hi
  exact linearIndependent_iff_injective_fintypeLinearCombination.mp hr

/-- An integral coordinate automorphism induces a real linear homeomorphism. -/
def realExponentEquiv {d : ℕ} (E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ)) :
    (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  (LinearEquiv.ofBijective (realExponentMap E.toLinearMap)
    ⟨realExponentMap_injective E.toLinearMap E.injective,
      LinearMap.surjective_of_injective (realExponentMap_injective E.toLinearMap E.injective)⟩).toContinuousLinearEquiv

theorem newtonPolytope_reindex {d : ℕ} (E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ))
    (f : MultiLaurent d) :
    newtonPolytope (AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f) =
      realExponentEquiv E '' newtonPolytope f :=
  newtonPolytope_map_injective E.toLinearMap.toAddMonoidHom E.injective
    (realExponentMap E.toLinearMap) (realExponentMap_exponentVector E.toLinearMap) f

theorem origin_interior_reindex {d : ℕ} (E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ))
    (f : MultiLaurent d) (hf : (0 : Fin d → ℝ) ∈ interior (newtonPolytope f)) :
    (0 : Fin d → ℝ) ∈
      interior (newtonPolytope (AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f)) := by
  rw [newtonPolytope_reindex]
  have he : realExponentEquiv E '' interior (newtonPolytope f) =
      interior (realExponentEquiv E '' newtonPolytope f) :=
    (realExponentEquiv E).toHomeomorph.image_interior _
  rw [← he]
  exact ⟨0, hf, map_zero _⟩

/-- A coordinate minimum of an origin-interior Newton polytope is strictly negative. -/
theorem coordinate_minimum_neg {d : ℕ} (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ interior (newtonPolytope f)) (v : Fin d → ℤ)
    (hmin : ∀ a ∈ f.coeff.support, ∀ i, v i ≤ a i) (i : Fin d) : v i < 0 := by
  by_contra! hnonneg
  have hsub : newtonPolytope f ⊆ (fun x : Fin d → ℝ => x i) ⁻¹' Ici 0 := by
    refine convexHull_min ?_ ((convex_Ici (0 : ℝ)).linear_preimage
      (LinearMap.proj i : (Fin d → ℝ) →ₗ[ℝ] ℝ))
    rintro _ ⟨a, ha, rfl⟩
    change 0 ≤ (a i : ℝ)
    exact_mod_cast hnonneg.trans (hmin a ha i)
  have hm := interior_mono hsub hf
  have he := (isOpenMap_eval (X := fun _ : Fin d => ℝ) i).preimage_interior_eq_interior_preimage (continuous_apply i) (Ici (0 : ℝ))
  rw [← he] at hm
  simp at hm

end
end DuistermaatVanDerKallen
