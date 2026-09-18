import DuistermaatVanDerKallen.LatticeCoordinates

/-! Full minimal-face reduction. Successive proper supporting cuts replace the
manuscript's one-step choice of the smallest face; the resulting lattice
coordinates prove the same statement, including the rank-zero alternative. -/

open Set
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

/-- A Laurent polytope with zero interior in its span admits integral coordinates
in which zero is in its full-dimensional interior. -/
theorem exists_interior_lattice_coordinates {d : ℕ} (f : MultiLaurent d)
    (hf : f ≠ 0) (hi : OriginInSpanInterior (newtonPolytope f)) :
    ∃ r ≤ d, ∃ g : MultiLaurent r, g ≠ 0 ∧
      (∀ n : ℕ, constantTerm (g ^ n) = constantTerm (f ^ n)) ∧
      (0 : Fin r → ℝ) ∈ interior (newtonPolytope g) := by
  let W := Submodule.span ℝ (newtonPolytope f)
  obtain ⟨r, ⟨b⟩⟩ := (integralLattice W).nonempty_basis_of_pid (Pi.basisFun ℤ (Fin d))
  obtain ⟨g, hg⟩ := exists_lattice_polynomial b f (by
    intro a ha
    exact Submodule.subset_span (subset_convexHull ℝ _ ⟨a, ha, rfl⟩))
  have hnewton : newtonPolytope f = latticeRealMap b '' newtonPolytope g := by
    rw [← hg]
    exact newtonPolytope_map_injective (latticeEmbedding b).toAddMonoidHom
      (latticeEmbedding_injective b) (latticeRealMap b) (latticeRealMap_exponentVector b) g
  have hrange : (latticeRealMap b).range = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact latticeRealMap_mem b x
    · apply Submodule.span_le.mpr
      rw [hnewton]
      rintro _ ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
  let F := (latticeRealMap b).codRestrict W (latticeRealMap_mem b)
  have hbij : Function.Bijective F := by
    constructor
    · intro x y h
      exact latticeRealMap_injective b (congrArg Subtype.val h)
    · intro y
      have hy : y.val ∈ (latticeRealMap b).range := hrange.symm ▸ y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  let e := (LinearEquiv.ofBijective F hbij).toContinuousLinearEquiv
  have hpre : e ⁻¹' (Subtype.val ⁻¹' newtonPolytope f) = newtonPolytope g := by
    ext x
    change latticeRealMap b x ∈ newtonPolytope f ↔ _
    rw [hnewton]
    constructor
    · rintro ⟨y, hy, he⟩
      exact latticeRealMap_injective b he ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨r, lattice_rank_le b, g, ?_, ?_, ?_⟩
  · intro he
    apply hf
    rw [← hg, he, map_zero]
  · intro n
    rw [← hg]
    exact (constantTerm_map_injective_pow (latticeEmbedding b).toAddMonoidHom
      (latticeEmbedding_injective b) g n).symm
  · have hm : (0 : Fin r → ℝ) ∈ e ⁻¹' interior (Subtype.val ⁻¹' newtonPolytope f) := by
      simpa [OriginInSpanInterior] using hi
    have heq : e ⁻¹' interior (Subtype.val ⁻¹' newtonPolytope f) =
        interior (e ⁻¹' (Subtype.val ⁻¹' newtonPolytope f)) :=
      e.toHomeomorph.preimage_interior _
    rw [heq, hpre] at hm
    exact hm

/-- All Laurent polynomials in zero variables are constants. -/
theorem rank_zero_eq_constant (f : MultiLaurent 0) :
    f = AddMonoidAlgebra.single 0 (constantTerm f) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  simp [ha, constantTerm]

/-- The manuscript's minimal-face reduction, with all nonnegative powers and
both rank alternatives. The statement is unconditional in every ambient rank. -/
theorem face_reduction {d : ℕ} (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ newtonPolytope f) :
    ∃ r ≤ d, ∃ g : MultiLaurent r,
      (∀ n : ℕ, constantTerm (g ^ n) = constantTerm (f ^ n)) ∧
      ((r = 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ g = AddMonoidAlgebra.single 0 c) ∨
        (1 ≤ r ∧ (0 : Fin r → ℝ) ∈ interior (newtonPolytope g))) := by
  obtain ⟨q, hq, _, _, hct, _, hi⟩ := exists_span_interior_restriction f hf
  obtain ⟨r, hr, g, hg, hgn, hgi⟩ := exists_interior_lattice_coordinates q hq hi
  refine ⟨r, hr, g, fun n => (hgn n).trans (hct n), ?_⟩
  by_cases hzero : r = 0
  · subst r
    refine Or.inl ⟨rfl, constantTerm g, ?_, rank_zero_eq_constant g⟩
    intro hc
    apply hg
    rw [rank_zero_eq_constant g, hc]
    simp
  · exact Or.inr ⟨by omega, hgi⟩


/-- The remaining minimal nonvanishing target in positive rank and full interior.
This is a proposition, not an assumed or proved analytic theorem. -/
def InteriorMinimalNonvanishing : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ f : MultiLaurent d,
    (0 : Fin d → ℝ) ∈ interior (newtonPolytope f) →
    ∃ n : ℕ, 1 ≤ n ∧ constantTerm (f ^ n) ≠ 0

/-- The complete face reduction removes all boundary and rank-zero cases from
the analytic minimal theorem. Its positive-rank interior premise remains open. -/
theorem minimal_of_interior_minimal (h : InteriorMinimalNonvanishing) :
    MinimalNonvanishing := by
  intro d f _ hf
  obtain ⟨r, _, g, hct, hcases⟩ := face_reduction f hf
  rcases hcases with ⟨_, c, hc, hgc⟩ | ⟨hr, hgi⟩
  · refine ⟨1, le_rfl, ?_⟩
    rw [← hct 1, pow_one, hgc]
    simpa [constantTerm] using hc
  · obtain ⟨n, hn, hne⟩ := h r hr g hgi
    exact ⟨n, hn, hct n ▸ hne⟩

/-- The original minimal theorem and its positive-rank interior version are
equivalent; neither side is asserted here without a premise. -/
theorem minimal_iff_interior_minimal : MinimalNonvanishing ↔ InteriorMinimalNonvanishing := by
  refine ⟨?_, minimal_of_interior_minimal⟩
  intro h d _ f hf
  have hm := interior_subset hf
  have hne : f ≠ 0 := by
    intro he
    rw [he] at hm
    simp [newtonPolytope] at hm
  exact h d f hne hm

end
end DuistermaatVanDerKallen
