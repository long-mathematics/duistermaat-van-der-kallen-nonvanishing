import DuistermaatVanDerKallen.DrivenPicard

/-! Local time-dependent horizontal ODE solutions from the driven Picard
construction. The base velocity is only assumed continuous in time. -/

open Set Metric
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- Return an anchored scaled curve to its actual time variable. -/
theorem laurent_unscale_driven_curve {d : ℕ} (f : MultiLaurent d)
    (a : ℝ → ℂ) (ha : Continuous a) (τ : CurveTime) (s δ : ℝ) (hδ : δ ≠ 0)
    {γ : ℝ → Fin d → ℂ}
    (hγ : ∀ t : CurveTime, γ t.val ∈ laurentRegularDomain f ∧
      HasDerivAt γ (δ • laurentVectorField f (rescaledVelocity a ha τ (s, δ) t) (γ t.val)) t.val) :
    ∀ t : ℝ, (t - s) / δ + τ.val ∈ Icc (0 : ℝ) 1 →
      γ ((t - s) / δ + τ.val) ∈ laurentRegularDomain f ∧
      HasDerivAt (fun u => γ ((u - s) / δ + τ.val))
        (laurentVectorField f (a t) (γ ((t - s) / δ + τ.val))) t := by
  intro t ht
  have h := hγ ⟨(t - s) / δ + τ.val, ht⟩
  refine ⟨h.1, ?_⟩
  have he : s + δ * (((t - s) / δ + τ.val) - τ.val) = t := by
    field_simp
    ring
  have hd := h.2.scomp t ((((hasDerivAt_id t).sub_const s).div_const δ).add_const τ.val)
  change HasDerivAt (fun u => γ ((u - s) / δ + τ.val))
    ((1 / δ) • (δ • laurentVectorField f
      (a (s + δ * (((t - s) / δ + τ.val) - τ.val)))
      (γ ((t - s) / δ + τ.val)))) t at hd
  simpa only [he, one_div, smul_smul, inv_mul_cancel₀ hδ, one_smul] using hd

/-- Uniform local existence for nearby start times and initial positions,
with a two-sided closed time interval contained in the regular domain. -/
theorem laurent_driven_local_existence {d : ℕ} (f : MultiLaurent d)
    (a : ℝ → ℂ) (ha : Continuous a) (s : ℝ)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ ρ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ t : ℝ, dist t s < ρ →
      ∀ y : Fin d → ℂ, dist y z < ρ →
        ∃ γ : ℝ → Fin d → ℂ, γ t = y ∧
          ∀ u ∈ Icc (t - ε) (t + ε), γ u ∈ laurentRegularDomain f ∧
            HasDerivAt γ (laurentVectorField f (a u) (γ u)) u := by
  let τ : CurveTime := ⟨1 / 2, by constructor <;> norm_num⟩
  obtain ⟨Ψ, Ω, hΩ, hbase, _, _, hspec⟩ := laurent_driven_local_family f τ a ha s hz
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hbase)
  refine ⟨R / 2, half_pos hR, R / 4, by positivity, ?_⟩
  intro t ht y hy
  have hq : (t, (R / 2, y)) ∈ Ω := by
    apply hball
    simp only [mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
    exact ⟨ht.trans (half_lt_self hR), by rw [abs_of_pos (half_pos hR)]; exact half_lt_self hR,
      hy.trans (half_lt_self hR)⟩
  obtain ⟨γ, hγ0, _, hγ⟩ := laurent_driven_picard_equation_solves_ode f τ
    (rescaledVelocity a ha τ (t, R / 2)) (R / 2) y (Ψ (t, (R / 2, y)))
    (hspec _ hq).1 (hspec _ hq).2
  refine ⟨fun u => γ ((u - t) / (R / 2) + τ.val), by simpa using hγ0, ?_⟩
  intro u hu
  apply laurent_unscale_driven_curve f a ha τ t (R / 2) (ne_of_gt (half_pos hR)) hγ
  change (u - t) / (R / 2) + 1 / 2 ∈ Icc (0 : ℝ) 1
  constructor
  · have hh : -(1 / 2 : ℝ) ≤ (u - t) / (R / 2) :=
      (le_div_iff₀ (half_pos hR)).mpr (by linarith [hu.1])
    linarith
  · have hh : (u - t) / (R / 2) ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ (half_pos hR)).mpr (by linarith [hu.2])
    linarith

/-- A compact time set and a compact subset of the regular torus admit one
local existence time, uniform in both the start time and the initial point. -/
theorem laurent_driven_uniform_time {d : ℕ} (f : MultiLaurent d)
    (a : ℝ → ℂ) (ha : Continuous a) {J : Set ℝ} {K : Set (Fin d → ℂ)}
    (hJ : IsCompact J) (hK : IsCompact K) (hKU : K ⊆ laurentRegularDomain f) :
    ∃ ε > (0 : ℝ), ∀ s ∈ J, ∀ z ∈ K,
      ∃ γ : ℝ → Fin d → ℂ, γ s = z ∧
        ∀ t ∈ Icc (s - ε) (s + ε), γ t ∈ laurentRegularDomain f ∧
          HasDerivAt γ (laurentVectorField f (a t) (γ t)) t := by
  classical
  let S : Set (ℝ × (Fin d → ℂ)) := J ×ˢ K
  have hS : IsCompact S := hJ.prod hK
  have hlocal (p : S) := laurent_driven_local_existence f a ha p.val.1 (hKU p.property.2)
  choose ρ hρ ε hε hsol using hlocal
  obtain ⟨F, hF⟩ := hS.elim_nhds_subcover'
    (fun p hp => ball p (ρ ⟨p, hp⟩)) (fun p hp => ball_mem_nhds p (hρ ⟨p, hp⟩))
  have hmin : ∀ F : Finset S, ∃ δ > (0 : ℝ), ∀ p ∈ F, δ ≤ ε p := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert p F _ ih =>
      obtain ⟨δ, hδ, hd⟩ := ih
      refine ⟨min (ε p) δ, lt_min (hε p) hδ, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hd q hq)
  obtain ⟨δ, hδ, hd⟩ := hmin F
  refine ⟨δ, hδ, ?_⟩
  intro s hs z hz
  obtain ⟨p, hp, hsp⟩ := mem_iUnion₂.mp (hF (show (s, z) ∈ S from ⟨hs, hz⟩))
  have hdist : dist s p.val.1 < ρ p ∧ dist z p.val.2 < ρ p := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hsp
  obtain ⟨γ, hγ0, hγ⟩ := hsol p s hdist.1 z hdist.2
  refine ⟨γ, hγ0, fun t ht => hγ t ?_⟩
  exact ⟨by linarith [ht.1, hd p hp], by linarith [ht.2, hd p hp]⟩

end
end DuistermaatVanDerKallen
