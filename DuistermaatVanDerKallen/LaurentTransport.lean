import DuistermaatVanDerKallen.LaurentGeometry
import DuistermaatVanDerKallen.ODEContinuation

/-! Existence of the manuscript's normalized-gradient transport throughout a
closed base segment. Compact control is proved for every partial solution before
applying continuation. Smooth dependence and the fiber diffeomorphism are separate. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- Complete segment existence for arbitrary Laurent polynomials. The curve is
defined on an open time interval containing `[0,1]`, and has the exact prescribed
base motion there. No completeness or compactness premise about the curve is assumed. -/
theorem laurent_complete_segment_of_compact_base {d : ℕ} (f : MultiLaurent d)
    (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) (a : ℂ)
    (Q : Set ℂ) (hQ : IsCompact Q)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, laurentEval f z + t • a ∈ Q)
    (hgood : ∀ c ∈ Q, c ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :
    ∃ δ > (0 : ℝ), ∃ b > (1 : ℝ), ∃ γ : ℝ → (Fin d → ℂ), γ 0 = z ∧
      ∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f a (γ t)) t ∧
        laurentEval f (γ t) = laurentEval f z + t • a := by
  obtain ⟨c, hc, hbound⟩ := laurent_uniform_gradient f Q hQ hgood
  let R := (1 + ‖torusEmbed z‖) * Real.exp (‖a‖ / c)
  let K := laurentControlledRegion f Q R
  have hK : IsCompact K := laurentControlledRegion_isCompact f Q hQ R
  have hKU : K ⊆ laurentRegularDomain f :=
    fun y hy => (laurentControlledRegion_regular f Q hc hbound y hy).1
  have hexp : 1 ≤ Real.exp (‖a‖ / c) :=
    Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg a) hc.le)
  have hzR : ‖torusEmbed z‖ ≤ R := by
    dsimp [R]
    nlinarith [norm_nonneg (torusEmbed z)]
  have hzQ : laurentEval f z ∈ Q := by simpa using hseg 0 (by simp)
  have hzK : z ∈ K := ⟨hz, hzR, hzQ⟩
  have hV : ∀ y ∈ laurentRegularDomain f, ContDiffAt ℝ 1 (laurentVectorField f a) y := by
    intro y hy
    exact (polynomialVectorField_contDiffAt_position (laurentRepresentative f) a hy).of_le (by simp)
  have hcontrol : ∀ (δ b : ℝ) (γ : ℝ → (Fin d → ℂ)), 0 < δ → 0 < b → b ≤ 1 →
      γ 0 = z →
      (∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f a (γ t)) t) → MapsTo γ (Ico 0 b) K := by
    intro δ b γ hδ hb hb1 hγ0 hd
    have hbase := laurent_integral_curve_base f a isOpen_Ioo isPreconnected_Ioo
      (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
      (s := 0) (by constructor <;> linarith)
    have hQt : ∀ t ∈ Ico 0 b, laurentEval f (γ t) ∈ Q := by
      intro t ht
      rw [hbase t ⟨by linarith [ht.1], ht.2⟩, hγ0, sub_zero]
      exact hseg t ⟨ht.1, ht.2.le.trans hb1⟩
    intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Ioo (-δ) b :=
      fun u hu => ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
    have hsmall : Icc (0 : ℝ) t ⊆ Ico 0 b :=
      fun u hu => ⟨hu.1, hu.2.trans_lt ht.2⟩
    have hgrowth := laurent_integral_curve_radius_bound f a hc
      (fun u hu => (hd u (hsub hu)).2.continuousAt.continuousWithinAt)
      (fun u hu => (hd u (hsub hu)).1)
      (fun u hu => (hd u (hsub (Ico_subset_Icc_self hu))).2)
      (fun u hu => hbound ⟨torusEmbed (γ u), embed_mem (hd u (hsub (Ico_subset_Icc_self hu))).1.1⟩
        (by
          change ambientEval (laurentRepresentative f) (torusEmbed (γ u)) ∈ Q
          rw [laurentRepresentative_eval]
          exact hQt u (hsmall (Ico_subset_Icc_self hu)))) t ⟨ht.1, le_rfl⟩
    have he : Real.exp ((‖a‖ / c) * t) ≤ Real.exp (‖a‖ / c) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_of_le_one_right (div_nonneg (norm_nonneg a) hc.le) (ht.2.le.trans hb1)
    have hr : ‖torusEmbed (γ t)‖ ≤ R := by
      rw [hγ0, sub_zero] at hgrowth
      have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1 + ‖torusEmbed z‖)
      dsimp [R]
      linarith
    exact ⟨(hd t ⟨by linarith [ht.1], ht.2⟩).1.1, hr, hQt t ht⟩
  obtain ⟨δ, hδ, b, hb, γ, hγ0, hd⟩ := ode_exists_past_of_compact_control
    (laurentRegularDomain_isOpen f) hK hKU hV (hKU hzK) 1 hcontrol
  refine ⟨δ, hδ, b, hb, γ, hγ0, ?_⟩
  have hbase := laurent_integral_curve_base f a isOpen_Ioo isPreconnected_Ioo
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
    (s := 0) (by constructor <;> linarith)
  intro t ht
  refine ⟨(hd t ht).1, (hd t ht).2, ?_⟩
  simpa [hγ0] using hbase t ht

/-- Complete existence with precisely the segment-exclusion hypothesis.
The auxiliary compact base is constructed as the image of `[0,1]`. -/
theorem laurent_complete_segment {d : ℕ} (f : MultiLaurent d)
    (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) (a : ℂ)
    (hgood : ∀ t ∈ Icc (0 : ℝ) 1, laurentEval f z + t • a ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :
    ∃ δ > (0 : ℝ), ∃ b > (1 : ℝ), ∃ γ : ℝ → (Fin d → ℂ), γ 0 = z ∧
      ∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f a (γ t)) t ∧
        laurentEval f (γ t) = laurentEval f z + t • a := by
  let σ : ℝ → ℂ := fun t => laurentEval f z + t • a
  have hσ : Continuous σ := by fun_prop
  exact laurent_complete_segment_of_compact_base f z hz a (σ '' Icc 0 1)
    (isCompact_Icc.image hσ) (fun t ht => ⟨t, ht, rfl⟩)
    (by rintro c ⟨t, ht, rfl⟩; exact hgood t ht)

/-- Uniqueness of Laurent segment solutions, including both endpoints. -/
theorem laurent_segment_unique {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ η : ℝ → (Fin d → ℂ)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f a (η t)) t)
    (hinit : γ 0 = η 0) : EqOn γ η (Icc (0 : ℝ) 1) :=
  ode_unique_on_closed_interval
    (fun y hy => (polynomialVectorField_contDiffAt_position
      (laurentRepresentative f) a hy).of_le (by simp))
    (fun t ht => (hγ t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hη t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hγ t (Ico_subset_Icc_self ht)).2)
    (fun t ht => (hη t (Ico_subset_Icc_self ht)).2)
    (fun t ht => (hγ t ht).1) (fun t ht => (hη t ht).1) hinit

/-- Reversing the base velocity negates the explicit scalar lift. -/
theorem laurentVectorField_neg {d : ℕ} (f : MultiLaurent d) (a : ℂ) (z : Fin d → ℂ) :
    laurentVectorField f (-a) z = -laurentVectorField f a z := by
  funext i
  simp only [laurentVectorField, polynomialVectorField, scalarLift, Pi.neg_apply]
  ring

/-- Time reversal of a segment solution solves the reversed normalized-gradient ODE. -/
theorem laurent_segment_reverse {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ : ℝ → (Fin d → ℂ)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ t)) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ (1 - t) ∈ laurentRegularDomain f ∧
      HasDerivAt (fun u => γ (1 - u)) (laurentVectorField f (-a) (γ (1 - t))) t := by
  intro t ht
  have hrev : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  refine ⟨(hγ _ hrev).1, ?_⟩
  rw [laurentVectorField_neg]
  simpa only [Function.comp_def, id_eq, neg_one_smul] using
    (hγ _ hrev).2.scomp t ((hasDerivAt_id t).const_sub 1)

/-- Any solution of the reversed segment retraces the forward solution.
This gives the inverse identity without presupposing a chosen global flow. -/
theorem laurent_segment_reverse_inverse {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ η : ℝ → (Fin d → ℂ)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f (-a) (η t)) t)
    (hinit : η 0 = γ 1) : EqOn η (fun t => γ (1 - t)) (Icc (0 : ℝ) 1) :=
  laurent_segment_unique f (-a) hη (laurent_segment_reverse f a hγ) (by simpa using hinit)

/-- Regression for a stationary base segment: its lift is the constant curve. -/
theorem laurent_zero_velocity_curve {d : ℕ} (f : MultiLaurent d)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) (t : ℝ) :
    z ∈ laurentRegularDomain f ∧
      HasDerivAt (fun _ : ℝ => z) (laurentVectorField f 0 z) t := by
  have hzero : laurentVectorField f 0 z = 0 := by
    funext i
    simp [laurentVectorField, polynomialVectorField, scalarLift]
  refine ⟨hz, ?_⟩
  rw [hzero]
  exact hasDerivAt_const t z

end
end DuistermaatVanDerKallen
