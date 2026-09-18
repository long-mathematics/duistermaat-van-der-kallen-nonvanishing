/-
SPDX-License-Identifier: Apache-2.0
The local Picard construction is adapted from mathlib's
Analysis/ODE/ExistUnique.lean and Analysis/ODE/PicardLindelof.lean.
Copyright (c) 2026 Winston Yin. All rights reserved.
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Authors of the upstream proofs: Yury Kudryashov, Winston Yin.
Modified here to retain range control and prove compact-domain continuation.
See LICENSES/Apache-2.0.txt and THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.ODE.ExistUnique

/-! Compact-domain continuation for autonomous real ODEs. The compact set lies
inside the regular domain; boundedness of positions alone is not the hypothesis.
The local Picard construction retains its closed-ball range bound. -/

open Set Metric Filter
open scoped Topology NNReal

namespace DuistermaatVanDerKallen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard's local solution, retaining the range bound used in its construction. -/
theorem picard_solution_with_range {V : ℝ → E → E} {l b : ℝ}
    {t₀ : Icc l b} {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof V t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ γ : ℝ → E, γ t₀ = x ∧
      (∀ t, γ t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Ioo l b, HasDerivAt γ (V t (γ t)) t := by
  obtain ⟨γ, hγ⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨γ.compProj, ?_, fun _ => γ.compProj_mem_closedBall hf.mul_max_le, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hγ, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply HasDerivWithinAt.hasDerivAt (s := Icc l b) _ (Icc_mem_nhds ht.1 ht.2)
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      γ.continuous_compProj.continuousOn
      (fun _ _ => γ.compProj_mem_closedBall hf.mul_max_le) x (Ioo_subset_Icc_self ht)
      |>.congr_of_mem _ (Ioo_subset_Icc_self ht)
    intro u hu
    nth_rw 1 [← hγ]
    rw [ODE.FunSpace.compProj_of_mem hu, ODE.FunSpace.next_apply]

/-- Local existence with a uniform starting neighborhood and a prescribed open
range. This strengthens the usual local existence statement by retaining control
inside the regular vector-field domain. -/
theorem local_ode_solution_in_open {V : E → E} {U : Set E} {x₀ : E}
    (hU : U ∈ 𝓝 x₀) (hV : ContDiffAt ℝ 1 V x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ ball x₀ r,
      ∃ γ : ℝ → E, γ 0 = x ∧
        ∀ t ∈ Ioo (-ε) ε, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t := by
  obtain ⟨K, s, hs, hLip⟩ := hV.exists_lipschitzOnWith
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hU)
  let L := (K : ℝ) * a + ‖V x₀‖ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hball : closedBall x₀ (a / 2) ⊆ s ∩ U :=
    (closedBall_subset_ball (half_lt_self ha)).trans has
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖V x‖ ≤ L := by
    calc
      ‖V x‖ ≤ ‖V x - V x₀‖ + ‖V x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖V x₀‖ :=
        add_le_add (hLip.norm_sub_le (hball hx).1 (mem_of_mem_nhds hs)) le_rfl
      _ ≤ K * a + ‖V x₀‖ := by
        gcongr
        exact mem_closedBall_iff_norm.mp ((closedBall_subset_closedBall (half_le_self ha.le)) hx)
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let aa : ℝ≥0 := ⟨a / 2, (half_pos ha).le⟩
  let rr : ℝ≥0 := aa / 2
  let LL : ℝ≥0 := ⟨L, hL.le⟩
  have hPL : IsPicardLindelof (fun _ => V)
      (tmin := -ε) (tmax := ε) ⟨0, by constructor <;> linarith⟩ x₀ aa rr LL K := by
    apply IsPicardLindelof.of_time_independent hb (hLip.mono fun x hx => (hball hx).1)
    change L * max (ε - 0) (0 - -ε) ≤ a / 2 - (a / 2) / 2
    simp only [sub_zero, sub_neg_eq_add, zero_add, max_self]
    have heq : L * ε = a / 4 := by
      dsimp [ε]
      field_simp
      ring
    rw [heq]
    linarith
  refine ⟨rr, by change 0 < a / 2 / 2; positivity, ε, hε, ?_⟩
  intro x hx
  obtain ⟨γ, hγ, hmem, hd⟩ := picard_solution_with_range hPL (ball_subset_closedBall hx)
  exact ⟨γ, hγ, fun t ht => ⟨(hball (hmem t)).2, hd t ht⟩⟩

/-- A compact subset of the regular domain has one uniform local existence time.
The curves stay in the domain, and the time does not depend on the initial point. -/
theorem uniform_ode_time_on_compact {V : E → E} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x) :
    ∃ ε > (0 : ℝ), ∀ x ∈ K, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t := by
  classical
  have hlocal (x : K) := local_ode_solution_in_open
    (hU.mem_nhds (hKU x.property)) (hV x (hKU x.property))
  choose r hr ε hε hsol using hlocal
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover'
    (fun x hx => ball x (r ⟨x, hx⟩)) (fun x hx => ball_mem_nhds x (hr ⟨x, hx⟩))
  have hmin : ∀ s : Finset K, ∃ δ > (0 : ℝ), ∀ x ∈ s, δ ≤ ε x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x s _ ih =>
      obtain ⟨δ, hδ, hd⟩ := ih
      refine ⟨min (ε x) δ, lt_min (hε x) hδ, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hd y hy)
  obtain ⟨δ, hδ, hd⟩ := hmin s
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  obtain ⟨γ, hγ, hcurve⟩ := hsol y x hxy
  refine ⟨γ, hγ, fun t ht => hcurve t ?_⟩
  exact ⟨(neg_le_neg (hd y hy)).trans_lt ht.1, ht.2.trans_le (hd y hy)⟩

omit [CompleteSpace E] in
/-- Smoothness near a compact set gives one Lipschitz constant on that set,
without any convexity assumption on the compact set itself. -/
theorem smooth_lipschitz_on_compact {V : E → E} {K : Set E}
    (hK : IsCompact K) (hV : ∀ x ∈ K, ContDiffAt ℝ 1 V x) :
    ∃ L, LipschitzOnWith L V K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨L, s, hs, hL⟩ := (hV x hx).exists_lipschitzOnWith
  exact ⟨L, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩

omit [CompleteSpace E] in
/-- Uniqueness on a closed interval for curves in an open smooth domain.
Only their compact images are used to obtain a common Lipschitz constant. -/
theorem ode_unique_on_closed_interval {V : E → E} {U : Set E}
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {γ η : ℝ → E} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hdγ : ∀ t ∈ Ico a b, HasDerivAt γ (V (γ t)) t)
    (hdη : ∀ t ∈ Ico a b, HasDerivAt η (V (η t)) t)
    (hmemγ : MapsTo γ (Icc a b) U) (hmemη : MapsTo η (Icc a b) U)
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  let K := γ '' Icc a b ∪ η '' Icc a b
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hγ).union (isCompact_Icc.image_of_continuousOn hη)
  have hKU : K ⊆ U := union_subset (image_subset_iff.mpr hmemγ) (image_subset_iff.mpr hmemη)
  obtain ⟨L, hL⟩ := smooth_lipschitz_on_compact hK (fun x hx => hV x (hKU hx))
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => K) (fun _ _ => hL)
    hγ (fun t ht => (hdγ t ht).hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    hη (fun t ht => (hdη t ht).hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) heq

omit [CompleteSpace E] in
/-- Uniqueness on an open interval, with any initial time in that interval. -/
theorem ode_unique_on_open_interval {V : E → E} {U : Set E}
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {γ η : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t)
    (hη : ∀ t ∈ Ioo a b, η t ∈ U ∧ HasDerivAt η (V (η t)) t)
    (heq : γ t₀ = η t₀) : EqOn γ η (Ioo a b) := by
  intro t ht
  let l := (a + min t t₀) / 2
  let r := (max t t₀ + b) / 2
  have hal : a < l := by dsimp [l]; linarith [lt_min ht.1 ht₀.1]
  have hrb : r < b := by dsimp [r]; linarith [max_lt ht.2 ht₀.2]
  have hlt : l < t := by dsimp [l]; linarith [min_le_left t t₀, ht.1]
  have hlt₀ : l < t₀ := by dsimp [l]; linarith [min_le_right t t₀, ht₀.1]
  have htr : t < r := by dsimp [r]; linarith [le_max_left t t₀, ht.2]
  have ht₀r : t₀ < r := by dsimp [r]; linarith [le_max_right t t₀, ht₀.2]
  have hsub : Icc l r ⊆ Ioo a b := fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  let K := γ '' Icc l r ∪ η '' Icc l r
  have hcγ : ContinuousOn γ (Icc l r) := fun x hx => (hγ x (hsub hx)).2.continuousAt.continuousWithinAt
  have hcη : ContinuousOn η (Icc l r) := fun x hx => (hη x (hsub hx)).2.continuousAt.continuousWithinAt
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hcγ).union
    (isCompact_Icc.image_of_continuousOn hcη)
  have hKU : K ⊆ U := by
    rintro x (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hγ u (hsub hu)).1
    · exact (hη u (hsub hu)).1
  obtain ⟨L, hL⟩ := smooth_lipschitz_on_compact hK (fun x hx => hV x (hKU hx))
  exact ODE_solution_unique_of_mem_Ioo (s := fun _ => K) (fun _ _ => hL) ⟨hlt₀, ht₀r⟩
    (fun u hu => ⟨(hγ u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inl ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩)
    (fun u hu => ⟨(hη u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inr ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩) heq ⟨hlt, htr⟩

omit [CompleteSpace E] in
/-- Translate a local autonomous solution from time zero to any initial time. -/
theorem shift_ode_solution {V : E → E} {U : Set E} {γ : ℝ → E} {ε : ℝ}
    (hγ : ∀ t ∈ Ioo (-ε) ε, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t) (s : ℝ) :
    ∀ t ∈ Ioo (s - ε) (s + ε),
      γ (t - s) ∈ U ∧ HasDerivAt (fun u => γ (u - s)) (V (γ (t - s))) t := by
  intro t ht
  have hu : t - s ∈ Ioo (-ε) ε := by constructor <;> linarith [ht.1, ht.2]
  refine ⟨(hγ _ hu).1, ?_⟩
  simpa only [Function.comp_def, id_eq, one_smul] using (hγ _ hu).2.scomp t ((hasDerivAt_id t).sub_const s)

omit [CompleteSpace E] in
/-- Glue overlapping solutions with a common value, retaining both restrictions. -/
theorem ode_glue_right {V : E → E} {U : Set E}
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {γ β : ℝ → E} {a b c d s : ℝ}
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t)
    (hβ : ∀ t ∈ Ioo c d, β t ∈ U ∧ HasDerivAt β (V (β t)) t)
    (hs : s ∈ Ioo a b ∩ Ioo c d) (hinit : γ s = β s) :
    ∃ η : ℝ → E, EqOn η γ (Ioo a b) ∧ EqOn η β (Ioo c d) ∧
      ∀ t ∈ Ioo a d, η t ∈ U ∧ HasDerivAt η (V (η t)) t := by
  classical
  have hsame : EqOn γ β (Ioo (max a c) (min b d)) :=
    ode_unique_on_open_interval hV
      ⟨max_lt hs.1.1 hs.2.1, lt_min hs.1.2 hs.2.2⟩
      (fun t ht => hγ t ⟨(le_max_left _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_left _ _)⟩)
      (fun t ht => hβ t ⟨(le_max_right _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_right _ _)⟩) hinit
  let η := (Ioo a b).piecewise γ β
  have hold : EqOn η γ (Ioo a b) := fun t ht => by simp [η, ht]
  have hnew : EqOn η β (Ioo c d) := by
    intro t ht
    by_cases h : t ∈ Ioo a b
    · rw [hold h]
      exact hsame ⟨max_lt h.1 ht.1, lt_min h.2 ht.2⟩
    · simp [η, h]
  refine ⟨η, hold, hnew, ?_⟩
  intro t ht
  by_cases ho : t ∈ Ioo a b
  · have hevent : η =ᶠ[𝓝 t] γ := by
      filter_upwards [isOpen_Ioo.mem_nhds ho] with u hu
      exact hold hu
    have hd := (hγ t ho).2.congr_of_eventuallyEq hevent
    rw [← hold ho] at hd
    exact ⟨by rw [hold ho]; exact (hγ t ho).1, hd⟩
  · have hn : t ∈ Ioo c d := by
      have hbt : b ≤ t := by simpa [mem_Ioo, ht.1] using ho
      exact ⟨by linarith [hs.1.2, hs.2.1], ht.2⟩
    have hevent : η =ᶠ[𝓝 t] β := by
      filter_upwards [isOpen_Ioo.mem_nhds hn] with u hu
      exact hnew hu
    have hd := (hβ t hn).2.congr_of_eventuallyEq hevent
    rw [← hnew hn] at hd
    exact ⟨by rw [hnew hn]; exact (hβ t hn).1, hd⟩

/-- A solution whose image stays in a compact subset of its regular domain
extends past a finite right endpoint. The extension agrees on the whole old
interval, not merely at one initial point. -/
theorem ode_extend_right_of_compact {V : E → E} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ K ∧ HasDerivAt γ (V (γ t)) t) :
    ∃ b' > b, ∃ η : ℝ → E, EqOn η γ (Ioo a b) ∧
      ∀ t ∈ Ioo a b', η t ∈ U ∧ HasDerivAt η (V (η t)) t := by
  obtain ⟨ε, hε, hlocal⟩ := uniform_ode_time_on_compact hU hK hKU hV
  let s := (max a (b - ε) + b) / 2
  have hm : max a (b - ε) < b := max_lt hab (by linarith)
  have has : a < s := by dsimp [s]; linarith [le_max_left a (b - ε)]
  have hsb : s < b := by dsimp [s]; linarith
  have hbs : b < s + ε := by dsimp [s]; linarith [le_max_right a (b - ε)]
  obtain ⟨β, hβ0, hβ⟩ := hlocal (γ s) (hγ s ⟨has, hsb⟩).1
  have hinit : γ s = β (s - s) := by simp [hβ0]
  obtain ⟨η, hold, _, hη⟩ := ode_glue_right hV
    (fun t ht => ⟨hKU (hγ t ht).1, (hγ t ht).2⟩) (shift_ode_solution hβ s)
    ⟨⟨has, hsb⟩, ⟨by linarith, by linarith⟩⟩ hinit
  exact ⟨s + ε, hbs, η, hold, hη⟩

/-- Compact a priori control of all partial solutions yields existence beyond
any prescribed finite time. No maximal-curve or global-existence premise is
assumed: the proof uses a supremum of reachable times and uniform local gluing. -/
theorem ode_exists_past_of_compact_control {V : E → E} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {x : E} (hx : x ∈ U) (T : ℝ)
    (hcontrol : ∀ (δ b : ℝ) (γ : ℝ → E), 0 < δ → 0 < b → b ≤ T → γ 0 = x →
      (∀ t ∈ Ioo (-δ) b, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t) →
      MapsTo γ (Ico 0 b) K) :
    ∃ δ > (0 : ℝ), ∃ b > T, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-δ) b, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t := by
  classical
  let S : Set ℝ := {b | 0 < b ∧ ∃ δ > (0 : ℝ), ∃ γ : ℝ → E, γ 0 = x ∧
    ∀ t ∈ Ioo (-δ) b, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t}
  obtain ⟨r, hr, ε₀, hε₀, hlocal₀⟩ := local_ode_solution_in_open (hU.mem_nhds hx) (hV x hx)
  obtain ⟨γ₀, hγ₀, hd₀⟩ := hlocal₀ x (mem_ball_self hr)
  have hεS : ε₀ ∈ S := ⟨hε₀, ε₀, hε₀, γ₀, hγ₀, hd₀⟩
  have hSne : S.Nonempty := ⟨ε₀, hεS⟩
  suffices ∃ b ∈ S, T < b by
    obtain ⟨b, ⟨_, δ, hδ, γ, hγ, hd⟩, hb⟩ := this
    exact ⟨δ, hδ, b, hb, γ, hγ, hd⟩
  by_contra hnot
  have hbound : ∀ b ∈ S, b ≤ T := by
    intro b hb
    by_contra hn
    exact hnot ⟨b, hb, lt_of_not_ge hn⟩
  have hbdd : BddAbove S := ⟨T, hbound⟩
  let c := sSup S
  have hc : 0 < c := hε₀.trans_le (le_csSup hbdd hεS)
  obtain ⟨ε, hε, hlocal⟩ := uniform_ode_time_on_compact hU hK hKU hV
  let s := max 0 (c - ε / 2)
  have hs0 : 0 ≤ s := le_max_left _ _
  have hsc : s < c := max_lt hc (by linarith)
  obtain ⟨b, hbS, hsb⟩ := exists_lt_of_lt_csSup hSne hsc
  obtain ⟨hb0, δ, hδ, γ, hγ, hdγ⟩ := hbS
  have hbS : b ∈ S := ⟨hb0, δ, hδ, γ, hγ, hdγ⟩
  have hγs : γ s ∈ K := hcontrol δ b γ hδ hb0 (hbound b hbS) hγ hdγ ⟨hs0, hsb⟩
  obtain ⟨β, hβ0, hdβ⟩ := hlocal (γ s) hγs
  have hsold : s ∈ Ioo (-δ) b := ⟨by linarith, hsb⟩
  have hinit : γ s = β (s - s) := by simp [hβ0]
  obtain ⟨η, hold, _, hdη⟩ := ode_glue_right hV hdγ (shift_ode_solution hdβ s)
    ⟨hsold, ⟨by linarith, by linarith⟩⟩ hinit
  have hη0 : η 0 = x := (hold ⟨by linarith, hb0⟩).trans hγ
  have hnew : s + ε ∈ S := ⟨by linarith, δ, hδ, η, hη0, hdη⟩
  have hcnew : s + ε ≤ c := le_csSup hbdd hnew
  have hnear : c - ε / 2 ≤ s := le_max_right _ _
  linarith

end
end DuistermaatVanDerKallen
