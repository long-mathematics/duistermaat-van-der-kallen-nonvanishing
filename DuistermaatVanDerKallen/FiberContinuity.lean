import DuistermaatVanDerKallen.FiberTransport

/-! Continuous dependence for the actual chosen Laurent transport trajectories.
A common proper-radius bound places the entire family in one compact regular
region. Gronwall then gives a Lipschitz estimate in the initial point. -/

open Set
open scoped Topology NNReal

namespace DuistermaatVanDerKallen

noncomputable section

/-- A common initial proper-radius bound controls all trajectories in one compact
subset of the regular domain, uniformly over the unit time interval. -/
theorem fiberCurves_compact_control {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (B : ℝ) :
    ∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ laurentRegularDomain f ∧
      ∀ z : LaurentFiber f s, ‖torusEmbed z.val‖ ≤ B →
        ∀ t ∈ Icc (0 : ℝ) 1, fiberCurve h z t ∈ K := by
  let σ : ℝ → ℂ := fun t => s + t • a
  let Q := σ '' Icc (0 : ℝ) 1
  have hQ : IsCompact Q := isCompact_Icc.image (by fun_prop : Continuous σ)
  have hgood : ∀ c ∈ Q, c ∉
      ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f) := by
    rintro c ⟨t, ht, rfl⟩
    exact h t ht
  obtain ⟨c, hc, hbound⟩ := laurent_uniform_gradient f Q hQ hgood
  let R := (1 + B) * Real.exp (‖a‖ / c)
  refine ⟨laurentControlledRegion f Q R, laurentControlledRegion_isCompact f Q hQ R,
    fun z hz => (laurentControlledRegion_regular f Q hc hbound z hz).1, ?_⟩
  intro z hz t ht
  have hd := (fiberCurve_spec h z).2
  have hQt : ∀ u ∈ Icc (0 : ℝ) 1, laurentEval f (fiberCurve h z u) ∈ Q := by
    intro u hu
    exact ⟨u, hu, (hd u hu).2.2.symm⟩
  have hgrowth := laurent_integral_curve_radius_bound f a hc
    (fun u hu => (hd u hu).2.1.continuousAt.continuousWithinAt)
    (fun u hu => (hd u hu).1)
    (fun u hu => (hd u (Ico_subset_Icc_self hu)).2.1)
    (fun u hu => hbound ⟨torusEmbed (fiberCurve h z u),
      embed_mem (hd u (Ico_subset_Icc_self hu)).1.1⟩ (by
        change ambientEval (laurentRepresentative f) (torusEmbed (fiberCurve h z u)) ∈ Q
        rw [laurentRepresentative_eval]
        exact hQt u (Ico_subset_Icc_self hu))) t ht
  rw [(fiberCurve_spec h z).1, sub_zero] at hgrowth
  have hr : ‖torusEmbed (fiberCurve h z t)‖ ≤ R := by
    have hmul : (1 + ‖torusEmbed z.val‖) * Real.exp ((‖a‖ / c) * t) ≤ R := by
      dsimp [R]
      apply mul_le_mul (by linarith [hz]) _ (Real.exp_pos _).le
        (by linarith [norm_nonneg (torusEmbed z.val)])
      exact Real.exp_le_exp.mpr
        (mul_le_of_le_one_right (div_nonneg (norm_nonneg a) hc.le) ht.2)
    linarith
  exact ⟨(hd t ht).1.1, hr, hQt t ht⟩

/-- Uniform Lipschitz dependence on the initial point, for a family with bounded
initial proper radius. The constant is independent of time in `[0,1]`. -/
theorem fiberCurves_lipschitz_initial {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (B : ℝ) :
    ∃ L : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) 1,
      LipschitzOnWith L (fun z : LaurentFiber f s => fiberCurve h z t)
        {z | ‖torusEmbed z.val‖ ≤ B} := by
  obtain ⟨K, hK, hKU, hmem⟩ := fiberCurves_compact_control h B
  obtain ⟨L, hL⟩ := smooth_lipschitz_on_compact hK (fun z hz =>
    (polynomialVectorField_contDiffAt_position (laurentRepresentative f) a (hKU hz)).of_le (by simp))
  refine ⟨⟨Real.exp L, (Real.exp_pos _).le⟩, ?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hdist := dist_le_of_trajectories_ODE_of_mem (s := fun _ => K)
    (v := fun _ => laurentVectorField f a) (fun _ _ => hL)
    (fun u hu => ((fiberCurve_spec h z).2 u hu).2.1.continuousAt.continuousWithinAt)
    (fun u hu => ((fiberCurve_spec h z).2 u (Ico_subset_Icc_self hu)).2.1.hasDerivWithinAt)
    (fun u hu => hmem z hz u (Ico_subset_Icc_self hu))
    (fun u hu => ((fiberCurve_spec h w).2 u hu).2.1.continuousAt.continuousWithinAt)
    (fun u hu => ((fiberCurve_spec h w).2 u (Ico_subset_Icc_self hu)).2.1.hasDerivWithinAt)
    (fun u hu => hmem w hw u (Ico_subset_Icc_self hu))
    (le_refl (dist (fiberCurve h z 0) (fiberCurve h w 0))) t ht
  rw [(fiberCurve_spec h z).1, (fiberCurve_spec h w).1, sub_zero] at hdist
  calc
    _ ≤ dist z.val w.val * Real.exp (L * t) := hdist
    _ ≤ dist z.val w.val * Real.exp L := by
      gcongr
      exact mul_le_of_le_one_right L.coe_nonneg ht.2
    _ = _ := by rw [mul_comm]; rfl

/-- Joint continuity in initial point and time on any bounded initial-radius set. -/
theorem fiberCurves_continuousOn_sublevel {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (B : ℝ) :
    ContinuousOn (fun p : LaurentFiber f s × ℝ => fiberCurve h p.1 p.2)
      ({z | ‖torusEmbed z.val‖ ≤ B} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨L, hL⟩ := fiberCurves_lipschitz_initial h B
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L _ hL
  intro z _ t ht
  exact ((fiberCurve_spec h z).2 t ht).2.1.continuousAt.continuousWithinAt

/-- Proper radius is continuous on each Laurent fiber. -/
theorem fiberProperRadius_continuous {d : ℕ} (f : MultiLaurent d) (s : ℂ) :
    Continuous (fun z : LaurentFiber f s => ‖torusEmbed z.val‖) := by
  apply Continuous.norm
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (torusEmbed_contDiffAt_real z.property.1).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- Joint continuous dependence on initial point and time throughout the segment. -/
theorem fiberCurves_continuousOn {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) :
    ContinuousOn (fun p : LaurentFiber f s × ℝ => fiberCurve h p.1 p.2)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp
  let B := ‖torusEmbed p.1.val‖ + 1
  have hb : ‖torusEmbed p.1.val‖ < B := lt_add_one _
  have hc := fiberCurves_continuousOn_sublevel h B p ⟨hb.le, hp.2⟩
  apply hc.mono_of_mem_nhdsWithin
  have hnear : {q : LaurentFiber f s × ℝ | ‖torusEmbed q.1.val‖ < B} ∈ 𝓝 p :=
    ((fiberProperRadius_continuous f s).comp continuous_fst).continuousAt
      (isOpen_Iio.mem_nhds hb)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with q hq hqt
  exact ⟨hq.le, hqt.2⟩

/-- Joint continuity with the closed time interval as a subtype. -/
theorem fiberCurves_continuous {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) :
    Continuous (fun p : LaurentFiber f s × Icc (0 : ℝ) 1 => fiberCurve h p.1 p.2) := by
  exact (fiberCurves_continuousOn h).comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    (fun p => ⟨mem_univ _, p.2.property⟩)

/-- Time-one transport is continuous in its initial point. -/
theorem fiberTransport_continuous {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : Continuous (fiberTransport h) := by
  apply Continuous.subtype_mk
  exact (fiberCurves_continuous h).comp
    (continuous_id.prodMk (continuous_const (y := (⟨1, by simp⟩ : Icc (0 : ℝ) 1))))

/-- Reversed time-one transport is continuous too. -/
theorem fiberTransportBack_continuous {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : Continuous (fiberTransportBack h) := by
  apply Continuous.subtype_mk
  exact (fiberCurves_continuous h.reverse).comp
    (continuous_id.prodMk (continuous_const (y := (⟨1, by simp⟩ : Icc (0 : ℝ) 1))))

/-- Segment transport is a homeomorphism of fibers. This statement makes no
claim of smoothness; smooth dependence is a separate remaining obligation. -/
def fiberTransportHomeomorph {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : LaurentFiber f s ≃ₜ LaurentFiber f (s + a) where
  toEquiv := fiberTransportEquiv h
  continuous_toFun := fiberTransport_continuous h
  continuous_invFun := fiberTransportBack_continuous h

/-- The sweep of any compact subset of the initial fiber is compact in the
original coordinate space. In particular, coordinates cannot reach zero. -/
theorem fiberSweep_isCompact {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (C : Set (LaurentFiber f s)) (hC : IsCompact C) :
    IsCompact ((fun p : LaurentFiber f s × Icc (0 : ℝ) 1 => fiberCurve h p.1 p.2) ''
      (C ×ˢ univ)) :=
  (hC.prod isCompact_univ).image (fiberCurves_continuous h)

/-- Every point of the compact sweep remains in the regular torus domain. -/
theorem fiberSweep_subset_regular {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (C : Set (LaurentFiber f s)) :
    ((fun p : LaurentFiber f s × Icc (0 : ℝ) 1 => fiberCurve h p.1 p.2) ''
      (C ×ˢ univ)) ⊆ laurentRegularDomain f := by
  rintro x ⟨⟨z, t⟩, _, rfl⟩
  exact ((fiberCurve_spec h z).2 t t.property).1

end
end DuistermaatVanDerKallen
