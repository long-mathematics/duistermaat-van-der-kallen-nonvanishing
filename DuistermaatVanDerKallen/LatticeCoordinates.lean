import DuistermaatVanDerKallen.RelativeFaceReduction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-! Integral lattice coordinates and their real linear extension. -/

open Set
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- Casting integral exponent vectors is integer linear. -/
def exponentLinearMap {d : ℕ} : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun := exponentVector
  map_add' := exponentVector_add
  map_smul' n a := by ext i; simp [exponentVector]

/-- The integral lattice lying in a real subspace. -/
def integralLattice {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) :
    Submodule ℤ (Fin d → ℤ) :=
  (W.restrictScalars ℤ).comap exponentLinearMap

/-- The inclusion in ambient exponent coordinates associated to a lattice basis. -/
def latticeEmbedding {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) :
    (Fin r → ℤ) →ₗ[ℤ] (Fin d → ℤ) :=
  (integralLattice W).subtype.comp b.equivFun.symm.toLinearMap

theorem latticeEmbedding_injective {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) :
    Function.Injective (latticeEmbedding b) :=
  Subtype.val_injective.comp b.equivFun.symm.injective

/-- Extend the integral basis vectors by real linear combinations. -/
def latticeRealMap {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Fintype.linearCombination ℝ (fun i => exponentVector (b i).val)

theorem latticeRealMap_injective {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) :
    Function.Injective (latticeRealMap b) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mp
  have hi := b.linearIndependent.map' (integralLattice W).subtype (by simp)
  exact linearIndependent_algebraMap_comp_iff.mpr hi

theorem latticeRealMap_exponentVector {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) (a : Fin r → ℤ) :
    latticeRealMap b (exponentVector a) = exponentVector (latticeEmbedding b a) := by
  change (∑ i, (a i : ℝ) • exponentVector (b i).val) =
    exponentLinearMap ((b.equivFun.symm a).val)
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  congr 1
  ext i j
  simp [exponentLinearMap, exponentVector]

theorem latticeRealMap_mem {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) (x : Fin r → ℝ) :
    latticeRealMap b x ∈ W := by
  change (∑ i, x i • exponentVector (b i).val) ∈ W
  apply Submodule.sum_mem
  intro i _
  exact W.smul_mem _ (b i).property

theorem lattice_rank_le {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) : r ≤ d := by
  have h := LinearMap.finrank_le_finrank_of_injective (latticeRealMap_injective b)
  simpa using h


/-- Injective changes of exponent group preserve all power constant terms. -/
theorem constantTerm_map_injective_pow {d r : ℕ}
    (E : (Fin r → ℤ) →+ (Fin d → ℤ)) (hE : Function.Injective E)
    (g : MultiLaurent r) (n : ℕ) :
    constantTerm ((AddMonoidAlgebra.mapDomainRingHom ℂ E g) ^ n) =
      constantTerm (g ^ n) := by
  rw [← map_pow]
  change (Finsupp.mapDomain E (g ^ n).coeff) 0 = _
  rw [← E.map_zero, Finsupp.mapDomain_apply_of_injective hE]
  rfl

/-- Newton polytopes transform by the real extension of an injective exponent map. -/
theorem newtonPolytope_map_injective {d r : ℕ}
    (E : (Fin r → ℤ) →+ (Fin d → ℤ)) (hE : Function.Injective E)
    (F : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hF : ∀ a, F (exponentVector a) = exponentVector (E a)) (g : MultiLaurent r) :
    newtonPolytope (AddMonoidAlgebra.mapDomainRingHom ℂ E g) =
      F '' newtonPolytope g := by
  classical
  unfold newtonPolytope
  rw [F.image_convexHull]
  congr 1
  change exponentVector '' (↑(Finsupp.mapDomain E g.coeff).support : Set (Fin d → ℤ)) = _
  rw [Finsupp.mapDomain_support_of_injective hE, Finset.coe_image]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext a
  exact (hF a).symm

/-- Every polynomial supported in a lattice is the image of a polynomial in its basis coordinates. -/
theorem exists_lattice_polynomial {d r : ℕ} {W : Submodule ℝ (Fin d → ℝ)}
    (b : Module.Basis (Fin r) ℤ (integralLattice W)) (f : MultiLaurent d)
    (hf : ∀ a ∈ f.coeff.support, exponentVector a ∈ W) :
    ∃ g : MultiLaurent r,
      AddMonoidAlgebra.mapDomainRingHom ℂ (latticeEmbedding b).toAddMonoidHom g = f := by
  refine ⟨AddMonoidAlgebra.comapDomain (latticeEmbedding b) (latticeEmbedding_injective b) f, ?_⟩
  apply AddMonoidAlgebra.mapDomain_comapDomain
  intro a ha
  let u : integralLattice W := ⟨a, hf a ha⟩
  refine ⟨b.equivFun u, ?_⟩
  change (b.equivFun.symm (b.equivFun u)).val = a
  rw [b.equivFun.symm_apply_apply]

end
end DuistermaatVanDerKallen
