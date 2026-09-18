import DuistermaatVanDerKallen.LaurentGeometry

/-! Polynomial extensions that agree on the closed affine torus have the same
true torus partials and induced restricted differential norm. The ambient
partial derivatives themselves need not agree. -/

namespace DuistermaatVanDerKallen
noncomputable section
open scoped Topology

theorem torusPartial_eval_eq_of_eqOn {d : ℕ} (p q : AmbientPolynomial d)
    (h : Set.EqOn (ambientEval p) (ambientEval q) (affineTorus d))
    {x : TorusAmbient d} (hx : x ∈ affineTorus d) (i : Fin d) :
    ambientEval (torusPartial p i) x = ambientEval (torusPartial q i) x := by
  classical
  let z : Fin d → ℂ := fun i => x (.inl i)
  have hz : ∀ i, z i ≠ 0 := affineTorus_coordinate_ne_zero hx
  have he : (ambientEval q ∘ torusEmbed) =ᶠ[𝓝 z] (ambientEval p ∘ torusEmbed) := by
    filter_upwards [(torusDomain_isOpen d).mem_nhds hz] with y hy
    exact (h (embed_mem hy)).symm
  have hD := ((polynomial_torus_hasFDerivAt p hz).congr_of_eventuallyEq he).unique
    (polynomial_torus_hasFDerivAt q hz)
  have hi := congrArg (fun D : (Fin d → ℂ) →L[ℂ] ℂ => D (Pi.single i 1)) hD
  simpa [coordinateDifferential_apply, embed_coordinates hx, z, Pi.single_apply, mul_ite] using hi

theorem ambientDifferentialNorm_eq_of_eqOn {d : ℕ} (p q : AmbientPolynomial d)
    (h : Set.EqOn (ambientEval p) (ambientEval q) (affineTorus d))
    {x : TorusAmbient d} (hx : x ∈ affineTorus d) :
    ambientDifferentialNorm (torusPartial p) x =
      ambientDifferentialNorm (torusPartial q) x := by
  simp only [ambientDifferentialNorm, differentialNormSq, torusPartial_eval_eq_of_eqOn p q h hx]

end
end DuistermaatVanDerKallen
