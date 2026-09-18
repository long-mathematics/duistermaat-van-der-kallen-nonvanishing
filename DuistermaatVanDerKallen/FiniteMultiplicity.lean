import DuistermaatVanDerKallen.SemialgebraicLineFamilies
import DuistermaatVanDerKallen.RadiusProjection

/-! Uniform bounds for finite fibers in arbitrary finite dimension, conditional
only on the explicit coordinate-projection obligation. Projecting each finite
fiber to its coordinate lines reduces the count to the proved one-dimensional
bounds. The parameter and target value are both retained for families of maps.
No integration inequality or higher-dimensional component theorem is asserted. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/-- Incidence description of a fiber coordinate projection, retaining parameters. -/
theorem semialgebraic_fiber_coordinate_image
    (hproj : SemialgebraicProjectionObligation) {ι κ : Type} [Finite ι] [Finite κ]
    {S : Set ((ι ⊕ κ) → ℝ)} (hS : IsSemialgebraic (ι ⊕ κ) S) (i : κ) :
    IsSemialgebraic (ι ⊕ Unit) {q | ∃ x : κ → ℝ,
      Sum.elim (fun j => q (.inl j)) x ∈ S ∧ x i = q (.inr ())} := by
  let g : (ι ⊕ κ) → MvPolynomial ((ι ⊕ Unit) ⊕ κ) ℝ :=
    Sum.elim (fun k => MvPolynomial.X (.inl (.inl k))) (fun k => MvPolynomial.X (.inr k))
  let T : Set (((ι ⊕ Unit) ⊕ κ) → ℝ) := {q |
    Sum.elim (fun k => q (.inl (.inl k))) (fun k => q (.inr k)) ∈ S ∧
      q (.inr i) = q (.inl (.inr ()))}
  have he (q : ((ι ⊕ Unit) ⊕ κ) → ℝ) : (fun j => MvPolynomial.eval q (g j)) =
      Sum.elim (fun k => q (.inl (.inl k))) (fun k => q (.inr k)) := by
    funext j
    cases j <;> simp [g]
  have hT : IsSemialgebraic ((ι ⊕ Unit) ⊕ κ) T := by
    have hU := hS.polynomial_preimage g
    have hV := IsSemialgebraic.eq (ι := ((ι ⊕ Unit) ⊕ κ))
      (MvPolynomial.X (.inr i)) (MvPolynomial.X (.inl (.inr ())))
    convert hU.inter hV using 1
    ext q
    simp only [T, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      MvPolynomial.eval_X, he]
  convert hproj (ι ⊕ Unit) κ T hT using 1
  ext q
  simp only [Set.mem_ofPred_eq, T, Sum.elim_inl, Sum.elim_inr]

theorem ncard_le_product_coordinate_images {κ : Type*} [Fintype κ]
    (S : Set (κ → ℝ)) (hS : S.Finite) :
    S.ncard ≤ ∏ i, ((fun x : κ → ℝ => x i) '' S).ncard := by
  classical
  let C (i : κ) := (fun x : κ → ℝ => x i) '' S
  let : ∀ i, Fintype (C i) := fun i => (hS.image _).fintype
  let f (x : S) : ∀ i, C i := fun i => ⟨x.val i, ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_pi, Nat.card_coe_set_eq] using h

/-- Conditional on coordinate projection only. The finite-cardinality conclusion
for arbitrary-dimensional fibers is obtained by bounding every coordinate image.
No Hardt premise, compactness, or global finiteness of all fibers is used. -/
theorem IsSemialgebraic.uniform_finite_fibers_of_projection
    (hproj : SemialgebraicProjectionObligation) {ι κ : Type} [Finite ι] [Fintype κ]
    {S : Set ((ι ⊕ κ) → ℝ)} (hS : IsSemialgebraic (ι ⊕ κ) S) :
    ∃ N : ℕ, ∀ a : ι → ℝ,
      ({x : κ → ℝ | Sum.elim a x ∈ S}).Finite →
      ({x : κ → ℝ | Sum.elim a x ∈ S}).ncard ≤ N := by
  classical
  have hb (i : κ) := (semialgebraic_fiber_coordinate_image hproj hS i).uniform_finite_line_fibers
  choose N hN using hb
  refine ⟨∏ i, N i, fun a ha => ?_⟩
  apply (ncard_le_product_coordinate_images _ ha).trans
  apply Finset.prod_le_prod
  intro i _
  have hi := hN i a
  change ((fun x : κ → ℝ => x i) '' {x : κ → ℝ | Sum.elim a x ∈ S}).Finite →
    ((fun x : κ → ℝ => x i) '' {x : κ → ℝ | Sum.elim a x ∈ S}).ncard ≤ N i at hi
  exact hi (ha.image _)

/-- Uniform finite multiplicity of a semialgebraic family of maps, keeping both
the set parameter and the target value as parameters of one graph. This is the
counting input only, not an integration or change-of-variables theorem. -/
theorem uniform_semialgebraic_finite_multiplicity
    (hproj : SemialgebraicProjectionObligation)
    {ι κ ν : Type} [Finite ι] [Fintype κ] [Finite ν]
    (E : (ι → ℝ) → Set (κ → ℝ)) (f : (ι → ℝ) → (κ → ℝ) → (ν → ℝ))
    (hgraph : IsSemialgebraic ((ι ⊕ ν) ⊕ κ) {q |
      (fun j => q (.inr j)) ∈ E (fun j => q (.inl (.inl j))) ∧
      f (fun j => q (.inl (.inl j))) (fun j => q (.inr j)) =
        (fun j => q (.inl (.inr j)))}) :
    ∃ N : ℕ, ∀ a : ι → ℝ, ∀ y : ν → ℝ,
      ({x | x ∈ E a ∧ f a x = y}).Finite →
      ({x | x ∈ E a ∧ f a x = y}).ncard ≤ N := by
  obtain ⟨N, hN⟩ := hgraph.uniform_finite_fibers_of_projection hproj
  refine ⟨N, fun a y => ?_⟩
  exact hN (Sum.elim a y)

end
end DuistermaatVanDerKallen
