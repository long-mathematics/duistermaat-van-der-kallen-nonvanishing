import DuistermaatVanDerKallen.SpherePathChain
import DuistermaatVanDerKallen.RadiusProjection
import DuistermaatVanDerKallen.CommonRadius
import DuistermaatVanDerKallen.LaurentGeometry

/-! The exact common-radius finiteness argument for the actual restricted
scalar differential, conditional on the still-open geometric inputs. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Filter
open scoped Topology

/-- An asymptotic sequence gives arbitrarily large radii with the exact
small-gradient and target-distance constraints. -/
theorem radiusApproximationSet_unbounded_of_asymptotic {d : ℕ} (p : AmbientPolynomial d)
    (g : Fin d → AmbientPolynomial d) {c : ℂ}
    (hc : c ∈ asymptoticCriticalValues (fun x : affineTorus d => ambientEval p x.val)
      (fun x => ‖x.val‖) (fun x => ambientDifferentialNorm g x.val))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ B : ℝ, ∃ R ∈ radiusApproximationSet p g c ε δ, B ≤ R := by
  obtain ⟨x, hr, hf, hg⟩ := hc
  intro B
  have hb := hr.eventually (eventually_ge_atTop (max B 2))
  have hsmall := hg.eventually (gt_mem_nhds hε)
  have hclose := (Metric.tendsto_nhds.mp hf) δ hδ
  obtain ⟨n, hn, hs, hd⟩ := (hb.and (hsmall.and hclose)).exists
  refine ⟨‖(x n).val‖, ⟨?_, (x n).val, (x n).property, rfl, hs.le, hd⟩,
    (le_max_left B 2).trans hn⟩
  linarith [le_max_right B 2]

/-- Normalization uses the full induced ambient norm. -/
theorem normalize_mem_smallGradientSphere {d : ℕ} (g : Fin d → AmbientPolynomial d)
    {x : TorusAmbient d} {R ε : ℝ} (hR : 0 < R) (hx : x ∈ affineTorus d)
    (hn : ‖x‖ = R) (hg : R * ambientDifferentialNorm g x ≤ ε) :
    R⁻¹ • x ∈ smallGradientSphere g R ε := by
  have hu : R • R⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  refine ⟨?_, by simpa only [hu] using hx, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hn, inv_mul_cancel₀ hR.ne']
  · simpa only [hu] using hg

/-- The main scalar asymptotic finiteness result, with the exact unresolved
radius-tail and finite-C1-path inputs exposed. -/
theorem finite_asymptoticCriticalValues_of_radius_and_paths
    (htail : RadiusTailObligation) (hpaths : SphereC1ChainObligation)
    {d : ℕ} (p : AmbientPolynomial d) :
    (asymptoticCriticalValues (fun x : affineTorus d => ambientEval p x.val)
      (fun x => ‖x.val‖) (fun x => ambientDifferentialNorm (torusPartial p) x.val)).Finite := by
  classical
  let K := asymptoticCriticalValues (fun x : affineTorus d => ambientEval p x.val)
    (fun x => ‖x.val‖) (fun x => ambientDifferentialNorm (torusPartial p) x.val)
  obtain ⟨N, hN, L, hL, hp⟩ := hpaths d (torusPartial p)
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  by_contra hinf
  let e := Set.Infinite.natEmbedding K hinf
  let c : Fin (N + 1) → ℂ := fun i => (e i).val
  have hc : Function.Injective c := fun i j h => Fin.ext (e.injective (Subtype.ext h))
  obtain ⟨η, hη, hsep⟩ := finite_uniform_separation c hc
  let ε := η / (8 * L)
  have hε : 0 < ε := div_pos hη (by positivity)
  have hsmall : L * ε < η / 4 := by
    have he : L * ε = η / 8 := by dsimp [ε]; field_simp
    rw [he]
    linarith
  have htails : ∀ i : Fin (N + 1), ∀ᶠ R in atTop,
      R ∈ radiusApproximationSet p (torusPartial p) (c i) ε (η / 8) := by
    intro i
    exact eventually_atTop.mpr (htail d p (torusPartial p) (c i) ε (η / 8) hε (by positivity)
      (radiusApproximationSet_unbounded_of_asymptotic p (torusPartial p) (e i).property hε (by positivity)))
  obtain ⟨R, hRall⟩ := (eventually_all.mpr htails).exists
  have hR : 1 < R := (hRall 0).1
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  choose x hx hn hg hd using fun i => (hRall i).2
  let u (i : Fin (N + 1)) : smallGradientSphere (torusPartial p) R ε :=
    ⟨R⁻¹ • x i, normalize_mem_smallGradientSphere _ hR0 (hx i) (hn i) (hg i)⟩
  have hu (i : Fin (N + 1)) : R • (u i).val = x i := by
    simp only [u, smul_smul, mul_inv_cancel₀ hR0.ne', one_smul]
  obtain ⟨label, _, hconnect⟩ := hp R ε hR hε
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => label (u i)) (by simp)
  obtain ⟨γ, hlen⟩ := hconnect (u i) (u j) heq
  have hdist := (γ.smallGradient_image_dist_le p hR0.le).trans
    (mul_le_mul_of_nonneg_left hlen hε.le)
  rw [hu i, hu j] at hdist
  have htri := dist_triangle4 (c i) (ambientEval p (x i)) (ambientEval p (x j)) (c j)
  rw [dist_comm (c i) (ambientEval p (x i))] at htri
  have hs := hsep i j hij
  have hi := hd i
  have hj := hd j
  nlinarith

/-- Specialized to the original Laurent evaluation and restricted differential.
Both geometric inputs remain open; this is conditional coverage only. -/
theorem laurent_finite_asymptotic_of_projection_and_paths
    (hproj : SemialgebraicProjectionObligation) (hpaths : SphereC1ChainObligation)
    {d : ℕ} (f : MultiLaurent d) :
    (asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f)).Finite :=
  finite_asymptoticCriticalValues_of_radius_and_paths
    (radiusTail_of_semialgebraic_projection hproj) hpaths (laurentRepresentative f)

end
end DuistermaatVanDerKallen
