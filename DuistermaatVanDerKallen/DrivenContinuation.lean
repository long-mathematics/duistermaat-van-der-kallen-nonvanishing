/-
SPDX-License-Identifier: Apache-2.0
Adapted from this project's ODEContinuation.lean. The inherited upstream notices
are retained here; the local driven Picard construction is implemented separately.
Copyright (c) 2026 Winston Yin. All rights reserved.
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Authors of the upstream proofs: Yury Kudryashov, Winston Yin.
Modified here for continuous scalar time-dependent velocities, using compactness
in both time and the regular spatial domain.
See LICENSES/Apache-2.0.txt and THIRD_PARTY_NOTICES.md.
-/

import DuistermaatVanDerKallen.DrivenLocalODE
import DuistermaatVanDerKallen.ODEContinuation

/-! Uniqueness and compact-domain continuation for a continuous scalar driving
velocity. Compactness controls both time and the regular spatial domain. -/

open Set Metric Filter
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- Spatial Lipschitz control uniform for a continuous velocity on a compact
time set and positions in a compact subset of the regular torus. -/
theorem laurent_driven_lipschitz_on_compact {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v) {J : Set ℝ} {K : Set (Fin d → ℂ)}
    (hJ : IsCompact J) (hK : IsCompact K) (hKU : K ⊆ laurentRegularDomain f) :
    ∃ L, ∀ t ∈ J, LipschitzOnWith L (laurentVectorField f (v t)) K := by
  let S : Set (ℂ × (Fin d → ℂ)) := (v '' J) ×ˢ K
  let V : ℂ × (Fin d → ℂ) → (Fin d → ℂ) := fun p => laurentVectorField f p.1 p.2
  have hS : IsCompact S := (hJ.image hv).prod hK
  have hloc : LocallyLipschitzOn S V := by
    intro p hp
    have h : ContDiffAt ℝ 1 V p :=
      (polynomialVectorField_contDiffAt (laurentRepresentative f) (hKU hp.2)).of_le le_top
    obtain ⟨L, U, hU, hL⟩ := h.exists_lipschitzOnWith
    exact ⟨L, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hS
  refine ⟨L, ?_⟩
  intro t ht
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  have hh := hL.dist_le_mul (v t, x) (show (v t, x) ∈ S from ⟨⟨t, ht, rfl⟩, hx⟩)
    (v t, y) (show (v t, y) ∈ S from ⟨⟨t, ht, rfl⟩, hy⟩)
  simpa only [V, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hh

/-- Uniqueness of regular time-dependent horizontal curves on an open interval. -/
theorem laurent_driven_unique_on_open_interval {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {γ η : ℝ → Fin d → ℂ} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hη : ∀ t ∈ Ioo a b, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f (v t) (η t)) t)
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
  have hKU : K ⊆ laurentRegularDomain f := by
    rintro x (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hγ u (hsub hu)).1
    · exact (hη u (hsub hu)).1
  obtain ⟨L, hL⟩ := laurent_driven_lipschitz_on_compact f v hv isCompact_Icc hK hKU
  exact ODE_solution_unique_of_mem_Ioo (s := fun _ => K) (fun u hu => hL u (Ioo_subset_Icc_self hu)) ⟨hlt₀, ht₀r⟩
    (fun u hu => ⟨(hγ u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inl ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩)
    (fun u hu => ⟨(hη u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inr ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩) heq ⟨hlt, htr⟩

/-- Uniqueness with initial data at the left end of a closed time interval. -/
theorem laurent_driven_unique_on_closed_interval {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {γ η : ℝ → Fin d → ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hdγ : ∀ t ∈ Ico a b, HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hdη : ∀ t ∈ Ico a b, HasDerivAt η (laurentVectorField f (v t) (η t)) t)
    (hmemγ : MapsTo γ (Icc a b) (laurentRegularDomain f))
    (hmemη : MapsTo η (Icc a b) (laurentRegularDomain f))
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  let K := γ '' Icc a b ∪ η '' Icc a b
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hγ).union (isCompact_Icc.image_of_continuousOn hη)
  have hKU : K ⊆ laurentRegularDomain f := union_subset (image_subset_iff.mpr hmemγ) (image_subset_iff.mpr hmemη)
  obtain ⟨L, hL⟩ := laurent_driven_lipschitz_on_compact f v hv isCompact_Icc hK hKU
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => K) (fun t ht => hL t (Ico_subset_Icc_self ht))
    hγ (fun t ht => (hdγ t ht).hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    hη (fun t ht => (hdη t ht).hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) heq

/-- Glue overlapping driven solutions using uniqueness, retaining both old
restrictions and the same prescribed time-dependent velocity. -/
theorem laurent_driven_glue_right {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {γ β : ℝ → Fin d → ℂ} {a b c e s : ℝ}
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hβ : ∀ t ∈ Ioo c e, β t ∈ laurentRegularDomain f ∧
      HasDerivAt β (laurentVectorField f (v t) (β t)) t)
    (hs : s ∈ Ioo a b ∩ Ioo c e) (hinit : γ s = β s) :
    ∃ η : ℝ → Fin d → ℂ, EqOn η γ (Ioo a b) ∧ EqOn η β (Ioo c e) ∧
      ∀ t ∈ Ioo a e, η t ∈ laurentRegularDomain f ∧
        HasDerivAt η (laurentVectorField f (v t) (η t)) t := by
  classical
  have hsame : EqOn γ β (Ioo (max a c) (min b e)) :=
    laurent_driven_unique_on_open_interval f v hv
      ⟨max_lt hs.1.1 hs.2.1, lt_min hs.1.2 hs.2.2⟩
      (fun t ht => hγ t ⟨(le_max_left _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_left _ _)⟩)
      (fun t ht => hβ t ⟨(le_max_right _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_right _ _)⟩) hinit
  let η := (Ioo a b).piecewise γ β
  have hold : EqOn η γ (Ioo a b) := fun t ht => by simp [η, ht]
  have hnew : EqOn η β (Ioo c e) := by
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
  · have hn : t ∈ Ioo c e := by
      have hbt : b ≤ t := by simpa [mem_Ioo, ht.1] using ho
      exact ⟨by linarith [hs.1.2, hs.2.1], ht.2⟩
    have hevent : η =ᶠ[𝓝 t] β := by
      filter_upwards [isOpen_Ioo.mem_nhds hn] with u hu
      exact hnew hu
    have hd := (hβ t hn).2.congr_of_eventuallyEq hevent
    rw [← hnew hn] at hd
    exact ⟨by rw [hnew hn]; exact (hβ t hn).1, hd⟩

/-- Compact control in the regular domain extends a driven solution beyond a
finite endpoint, agreeing with the complete old open interval. -/
theorem laurent_driven_extend_right_of_compact {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v) {K : Set (Fin d → ℂ)}
    (hK : IsCompact K) (hKU : K ⊆ laurentRegularDomain f)
    {γ : ℝ → Fin d → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ K ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t) :
    ∃ b' > b, ∃ η : ℝ → Fin d → ℂ, EqOn η γ (Ioo a b) ∧
      ∀ t ∈ Ioo a b', η t ∈ laurentRegularDomain f ∧
        HasDerivAt η (laurentVectorField f (v t) (η t)) t := by
  obtain ⟨ε, hε, hlocal⟩ := laurent_driven_uniform_time f v hv (J := Icc a b) isCompact_Icc hK hKU
  let s := (max a (b - ε) + b) / 2
  have hm : max a (b - ε) < b := max_lt hab (by linarith)
  have has : a < s := by dsimp [s]; linarith [le_max_left a (b - ε)]
  have hsb : s < b := by dsimp [s]; linarith
  have hbs : b < s + ε := by dsimp [s]; linarith [le_max_right a (b - ε)]
  obtain ⟨β, hβ0, hβ⟩ := hlocal s ⟨has.le, hsb.le⟩ (γ s) (hγ s ⟨has, hsb⟩).1
  obtain ⟨η, hold, _, hη⟩ := laurent_driven_glue_right f v hv
    (fun t ht => ⟨hKU (hγ t ht).1, (hγ t ht).2⟩)
    (fun t ht => hβ t (Ioo_subset_Icc_self ht))
    ⟨⟨has, hsb⟩, ⟨by linarith, by linarith⟩⟩ hβ0.symm
  exact ⟨s + ε, hbs, η, hold, hη⟩

/-- A priori compact regular-domain control of all partial driven solutions
implies complete existence beyond any given finite time. -/
theorem laurent_driven_exists_past_of_compact_control {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v) {K : Set (Fin d → ℂ)}
    (hK : IsCompact K) (hKU : K ⊆ laurentRegularDomain f)
    {x : Fin d → ℂ} (hx : x ∈ laurentRegularDomain f) (T : ℝ)
    (hcontrol : ∀ (δ b : ℝ) (γ : ℝ → Fin d → ℂ), 0 < δ → 0 < b → b ≤ T → γ 0 = x →
      (∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (v t) (γ t)) t) →
      MapsTo γ (Ico 0 b) K) :
    ∃ δ > (0 : ℝ), ∃ b > T, ∃ γ : ℝ → Fin d → ℂ, γ 0 = x ∧
      ∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (v t) (γ t)) t := by
  classical
  let S : Set ℝ := {b | 0 < b ∧ ∃ δ > (0 : ℝ), ∃ γ : ℝ → Fin d → ℂ, γ 0 = x ∧
    ∀ t ∈ Ioo (-δ) b, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t}
  obtain ⟨ρ, hρ, ε₀, hε₀, hlocal₀⟩ := laurent_driven_local_existence f v hv 0 hx
  obtain ⟨γ₀, hγ₀, hc₀⟩ := hlocal₀ 0 (by simpa using hρ) x (by simpa using hρ)
  have hd₀ : ∀ t ∈ Ioo (-ε₀) ε₀, γ₀ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ₀ (laurentVectorField f (v t) (γ₀ t)) t := by
    intro t ht
    exact hc₀ t (by simpa using Ioo_subset_Icc_self ht)
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
  obtain ⟨ε, hε, hlocal⟩ := laurent_driven_uniform_time f v hv (J := Icc 0 T) isCompact_Icc hK hKU
  let s := max 0 (c - ε / 2)
  have hs0 : 0 ≤ s := le_max_left _ _
  have hsc : s < c := max_lt hc (by linarith)
  obtain ⟨b, hbS, hsb⟩ := exists_lt_of_lt_csSup hSne hsc
  obtain ⟨hb0, δ, hδ, γ, hγ, hdγ⟩ := hbS
  have hbS : b ∈ S := ⟨hb0, δ, hδ, γ, hγ, hdγ⟩
  have hγs : γ s ∈ K := hcontrol δ b γ hδ hb0 (hbound b hbS) hγ hdγ ⟨hs0, hsb⟩
  obtain ⟨β, hβ0, hdβ⟩ := hlocal s ⟨hs0, hsb.le.trans (hbound b hbS)⟩ (γ s) hγs
  have hsold : s ∈ Ioo (-δ) b := ⟨by linarith, hsb⟩
  obtain ⟨η, hold, _, hdη⟩ := laurent_driven_glue_right f v hv hdγ
    (fun t ht => hdβ t (Ioo_subset_Icc_self ht))
    ⟨hsold, ⟨by linarith, by linarith⟩⟩ hβ0.symm
  have hη0 : η 0 = x := (hold ⟨by linarith, hb0⟩).trans hγ
  have hnew : s + ε ∈ S := ⟨by linarith, δ, hδ, η, hη0, hdη⟩
  have hcnew : s + ε ≤ c := le_csSup hbdd hnew
  have hnear : c - ε / 2 ≤ s := le_max_right _ _
  linarith

end
end DuistermaatVanDerKallen
