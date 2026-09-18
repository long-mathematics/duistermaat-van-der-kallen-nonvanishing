import DuistermaatVanDerKallen.DrivenContinuation

/-! Complete transport along a continuously differentiable scalar base path.
The proper-radius estimate and separation from the critical locus are proved
for every partial solution before compact-domain continuation is applied. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- The horizontal ODE follows the prescribed base path exactly. One-sided
base derivatives on a closed convex time interval are sufficient. -/
theorem laurent_driven_curve_base {d : ℕ} (f : MultiLaurent d)
    (α v : ℝ → ℂ) {γ : ℝ → Fin d → ℂ} {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ t ∈ I, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hα : ∀ t ∈ I, HasDerivWithinAt α (v t) I t)
    {s : ℝ} (hs : s ∈ I) (hinit : laurentEval f (γ s) = α s) :
    ∀ t ∈ I, laurentEval f (γ t) = α t := by
  have hd : ∀ t ∈ I, HasDerivWithinAt (fun u => laurentEval f (γ u) - α u) 0 I t := by
    intro t ht
    simpa only [sub_self, Pi.sub_def, Function.comp_def] using
      (laurent_integral_curve_base_derivative f (v t) (hγ t ht).1 (hγ t ht).2).hasDerivWithinAt.sub
        (hα t ht)
  intro t ht
  have hh := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd (fun _ _ => by simp) hs ht
  simpa only [hinit, sub_self, sub_zero, norm_le_zero_iff, zero_mul, sub_eq_zero] using hh

/-- The proper embedded radius obeys Gronwall with a uniform bound on the
continuous driving velocity, not the ordinary coordinate-space radius. -/
theorem laurent_driven_curve_radius_bound {d : ℕ} (f : MultiLaurent d) (v : ℝ → ℂ)
    {γ : ℝ → Fin d → ℂ} {s b c B : ℝ} (hc : 0 < c)
    (hγ : ContinuousOn γ (Icc s b))
    (hz : ∀ t ∈ Icc s b, γ t ∈ laurentRegularDomain f)
    (hd : ∀ t ∈ Ico s b, HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hv : ∀ t ∈ Ico s b, ‖v t‖ ≤ B)
    (hbound : ∀ t (ht : t ∈ Ico s b),
      c ≤ (1 + ‖torusEmbed (γ t)‖) * laurentDifferentialNorm f
        ⟨torusEmbed (γ t), embed_mem (hz t (Ico_subset_Icc_self ht)).1⟩) :
    ∀ t ∈ Icc s b, 1 + ‖torusEmbed (γ t)‖ ≤
      (1 + ‖torusEmbed (γ s)‖) * Real.exp ((B / c) * (t - s)) := by
  apply trajectory_radius_bound (x := torusEmbed ∘ γ)
    (v := fun t => torusTangentMap (γ t) (laurentVectorField f (v t) (γ t)))
  · intro t ht
    exact (torusEmbed_contDiffAt_real (hz t ht).1).continuousAt.comp_continuousWithinAt (hγ t ht)
  · intro t ht
    exact (((torusEmbed_hasFDerivAt (hz t (Ico_subset_Icc_self ht)).1).restrictScalars ℝ).comp_hasDerivAt t (hd t ht)).hasDerivWithinAt
  · intro t ht
    exact (laurentVectorField_linear_growth f (v t) (hz t (Ico_subset_Icc_self ht)) hc
      (hbound t ht)).trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hv t ht) hc.le) (by positivity))

/-- Complete existence for a prescribed base path, with an open solution
interval around the whole unit interval. Compact regular-domain control is
proved from the path hypotheses and is not an additional premise. -/
theorem laurent_complete_driven_path {d : ℕ} (f : MultiLaurent d)
    (α v : ℝ → ℂ) (hv : Continuous v)
    (hα : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt α (v t) (Icc 0 1) t)
    (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) (hzα : laurentEval f z = α 0)
    (hgood : ∀ t ∈ Icc (0 : ℝ) 1, α t ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :
    ∃ δ > (0 : ℝ), ∃ b > (1 : ℝ), ∃ γ : ℝ → Fin d → ℂ, γ 0 = z ∧
      (∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (v t) (γ t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, laurentEval f (γ t) = α t := by
  let Q : Set ℂ := α '' Icc (0 : ℝ) 1
  have hQ : IsCompact Q := isCompact_Icc.image_of_continuousOn
    (fun t ht => (hα t ht).continuousWithinAt)
  have hgoodQ : ∀ c ∈ Q, c ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f) := by
    rintro c ⟨t, ht, rfl⟩
    exact hgood t ht
  obtain ⟨c, hc, hbound⟩ := laurent_uniform_gradient f Q hQ hgoodQ
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.continuousOn : ContinuousOn v (Icc (0 : ℝ) 1))
  have hB0 : 0 ≤ B := (norm_nonneg (v 0)).trans (hB 0 (by simp))
  let R := (1 + ‖torusEmbed z‖) * Real.exp (B / c)
  let K := laurentControlledRegion f Q R
  have hK : IsCompact K := laurentControlledRegion_isCompact f Q hQ R
  have hKU : K ⊆ laurentRegularDomain f :=
    fun y hy => (laurentControlledRegion_regular f Q hc hbound y hy).1
  have hexp : 1 ≤ Real.exp (B / c) := Real.one_le_exp_iff.mpr (div_nonneg hB0 hc.le)
  have hzR : ‖torusEmbed z‖ ≤ R := by
    dsimp [R]
    nlinarith [norm_nonneg (torusEmbed z)]
  have hzK : z ∈ K := ⟨hz, hzR, ⟨0, by simp, hzα.symm⟩⟩
  have hcontrol : ∀ (δ b : ℝ) (γ : ℝ → Fin d → ℂ), 0 < δ → 0 < b → b ≤ 1 → γ 0 = z →
      (∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (v t) (γ t)) t) → MapsTo γ (Ico 0 b) K := by
    intro δ b γ hδ hb hb1 hγ0 hd
    have hQt : ∀ t ∈ Ico (0 : ℝ) b, laurentEval f (γ t) ∈ Q := by
      intro t ht
      have hsub : Icc (0 : ℝ) t ⊆ Ioo (-δ) b :=
        fun u hu => ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
      have hunit : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 :=
        fun u hu => ⟨hu.1, hu.2.trans (ht.2.le.trans hb1)⟩
      have he := laurent_driven_curve_base f α v (convex_Icc 0 t) (fun u hu => hd u (hsub hu))
        (fun u hu => (hα u (hunit hu)).mono hunit) (s := 0) (by simp [ht.1])
        (by simpa only [hγ0] using hzα) t ⟨ht.1, le_rfl⟩
      exact ⟨t, ⟨ht.1, ht.2.le.trans hb1⟩, he.symm⟩
    intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Ioo (-δ) b :=
      fun u hu => ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
    have hsmall : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) b :=
      fun u hu => ⟨hu.1, hu.2.trans_lt ht.2⟩
    have hgrowth := laurent_driven_curve_radius_bound f v hc
      (fun u hu => (hd u (hsub hu)).2.continuousAt.continuousWithinAt)
      (fun u hu => (hd u (hsub hu)).1)
      (fun u hu => (hd u (hsub (Ico_subset_Icc_self hu))).2)
      (fun u hu => hB u ⟨hu.1, hu.2.le.trans (ht.2.le.trans hb1)⟩)
      (fun u hu => hbound ⟨torusEmbed (γ u), embed_mem (hd u (hsub (Ico_subset_Icc_self hu))).1.1⟩
        (by
          change ambientEval (laurentRepresentative f) (torusEmbed (γ u)) ∈ Q
          rw [laurentRepresentative_eval]
          exact hQt u (hsmall (Ico_subset_Icc_self hu)))) t ⟨ht.1, le_rfl⟩
    have he : Real.exp ((B / c) * t) ≤ Real.exp (B / c) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_of_le_one_right (div_nonneg hB0 hc.le) (ht.2.le.trans hb1)
    have hr : ‖torusEmbed (γ t)‖ ≤ R := by
      rw [hγ0, sub_zero] at hgrowth
      have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1 + ‖torusEmbed z‖)
      dsimp [R]
      linarith
    exact ⟨(hd t ⟨by linarith [ht.1], ht.2⟩).1.1, hr, hQt t ht⟩
  obtain ⟨δ, hδ, b, hb, γ, hγ0, hd⟩ :=
    laurent_driven_exists_past_of_compact_control f v hv hK hKU (hKU hzK) 1 hcontrol
  refine ⟨δ, hδ, b, hb, γ, hγ0, hd, ?_⟩
  exact laurent_driven_curve_base f α v (convex_Icc 0 1)
    (fun t ht => hd t ⟨by linarith [ht.1], ht.2.trans_lt hb⟩) hα
    (s := 0) (by simp) (by simpa only [hγ0] using hzα)

/-- Complete horizontal lifting for a C¹ path on the closed unit interval.
The velocity is continuous only on that interval, and endpoint derivatives of
the base path are one-sided. No global extension hypothesis is imposed. -/
theorem laurent_complete_C1_path {d : ℕ} (f : MultiLaurent d)
    (α v : ℝ → ℂ) (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    (hα : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt α (v t) (Icc 0 1) t)
    (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) (hzα : laurentEval f z = α 0)
    (hgood : ∀ t ∈ Icc (0 : ℝ) 1, α t ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :
    ∃ γ : ℝ → Fin d → ℂ, γ 0 = z ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (v t) (γ t)) t ∧
        laurentEval f (γ t) = α t := by
  let vC : C(CurveTime, ℂ) := ⟨fun t => v t.val, continuousOn_iff_continuous_domRestrict.mp hv⟩
  have he : ∀ t ∈ Icc (0 : ℝ) 1, extendCurve vC t = v t := by
    intro t ht
    exact extendCurve_apply vC ⟨t, ht⟩
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt α (extendCurve vC t) (Icc 0 1) t := by
    intro t ht
    rw [he t ht]
    exact hα t ht
  obtain ⟨δ, hδ, b, hb, γ, hγ0, hγ, hbase⟩ :=
    laurent_complete_driven_path f α (extendCurve vC) (extendCurve vC).continuous hd z hz hzα hgood
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  have h := hγ t ⟨by linarith [ht.1], ht.2.trans_lt hb⟩
  exact ⟨h.1, by simpa only [he t ht] using h.2, hbase t ht⟩

end
end DuistermaatVanDerKallen
