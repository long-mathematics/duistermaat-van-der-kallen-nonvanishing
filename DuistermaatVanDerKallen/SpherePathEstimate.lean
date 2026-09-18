import DuistermaatVanDerKallen.PolynomialCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tangency and integration along paths in the exact small-gradient sphere
family. The derivative bound uses the restricted induced-metric norm. -/

namespace DuistermaatVanDerKallen
noncomputable section

theorem curve_derivative_mem_torusTangentSpace {d : ℕ} {γ : ℝ → TorusAmbient d}
    {v : TorusAmbient d} {S : Set ℝ} {t : ℝ} (ht : t ∈ S)
    (hS : UniqueDiffWithinAt ℝ S t) (hγ : HasDerivWithinAt γ v S t)
    (hX : ∀ s ∈ S, γ s ∈ affineTorus d) :
    v ∈ torusTangentSpace (fun i => γ t (.inl i)) := by
  have hz := affineTorus_coordinate_ne_zero (hX t ht)
  rw [mem_torusTangentSpace_iff_linearized hz]
  intro i
  have hc (j : Fin d ⊕ Fin d) : HasDerivWithinAt (fun s => γ s j) (v j) S t :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d ⊕ Fin d => ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hγ
  have hp := (hc (.inl i)).mul (hc (.inr i))
  have hconst : HasDerivWithinAt (fun s => γ s (.inl i) * γ s (.inr i)) 0 S t :=
    (hasDerivWithinAt_const t S (1 : ℂ)).congr (fun s hs => hX s hs i) (hX t ht i)
  have he := (hp.derivWithin hS).symm.trans (hconst.derivWithin hS)
  rw [← affineTorus_inverse_coordinate (hX t ht) i]
  simpa [mul_comm] using he

theorem polynomialDifferential_norm_le_on_tangent {d : ℕ} (p : AmbientPolynomial d)
    {x v : TorusAmbient d} (hx : x ∈ affineTorus d)
    (hv : v ∈ torusTangentSpace (fun i => x (.inl i))) :
    ‖polynomialDifferential p x v‖ ≤
      ambientDifferentialNorm (torusPartial p) x * ‖v‖ := by
  have hnorm := polynomial_restricted_norm p (affineTorus_coordinate_ne_zero hx)
  rw [embed_coordinates hx] at hnorm
  have h := ((polynomialDifferential p x).comp
    (torusTangentSpace (fun i => x (.inl i))).subtypeL).le_opNorm ⟨v, hv⟩
  rwa [hnorm] at h

theorem smallGradient_curve_derivative_norm_le {d : ℕ} (p : AmbientPolynomial d)
    {γ : ℝ → TorusAmbient d} {v : TorusAmbient d} {S : Set ℝ} {t R ε : ℝ}
    (ht : t ∈ S) (hS : UniqueDiffWithinAt ℝ S t) (hR : 0 ≤ R)
    (hγ : HasDerivWithinAt γ v S t)
    (hX : ∀ s ∈ S, γ s ∈ smallGradientSphere (torusPartial p) R ε) :
    ‖polynomialDifferential p (R • γ t) (R • v)‖ ≤ ε * ‖v‖ := by
  have hx : ∀ s ∈ S, R • γ s ∈ affineTorus d := fun s hs => (hX s hs).2.1
  have hv := curve_derivative_mem_torusTangentSpace ht hS (hγ.const_smul R) hx
  have h := polynomialDifferential_norm_le_on_tangent p (hx t ht) hv
  calc
    _ ≤ ambientDifferentialNorm (torusPartial p) (R • γ t) * (R * ‖v‖) := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR] using h
    _ = (R * ambientDifferentialNorm (torusPartial p) (R • γ t)) * ‖v‖ := by ring
    _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right (hX t ht).2.2 (norm_nonneg v)

theorem smallGradient_curve_hasDerivWithinAt {d : ℕ} (p : AmbientPolynomial d)
    {γ : ℝ → TorusAmbient d} {v : TorusAmbient d} {S : Set ℝ} {t R : ℝ}
    (hγ : HasDerivWithinAt γ v S t) :
    HasDerivWithinAt (fun s => ambientEval p (R • γ s))
      (polynomialDifferential p (R • γ t) (R • v)) S t := by
  have hF : HasFDerivAt (ambientEval p) ((polynomialDifferential p (R • γ t)).restrictScalars ℝ)
      (R • γ t) := (ambientEval_hasFDerivAt p _).restrictScalars ℝ
  exact hF.comp_hasDerivWithinAt t (hγ.const_smul R)

theorem smallGradient_curve_image_bound {d : ℕ} (p : AmbientPolynomial d)
    {γ v : ℝ → TorusAmbient d} {R ε L : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt γ (v t) (Set.Icc 0 1) t)
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ smallGradientSphere (torusPartial p) R ε)
    (hV : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖v t‖ ≤ L) :
    ‖ambientEval p (R • γ 1) - ambientEval p (R • γ 0)‖ ≤ ε * L := by
  apply norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => smallGradient_curve_hasDerivWithinAt p (hγ t ht))
  intro t ht
  have ht' := Set.Ico_subset_Icc_self ht
  exact (smallGradient_curve_derivative_norm_le p ht'
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht') hR (hγ t ht') hX).trans
      (mul_le_mul_of_nonneg_left (hV t ht') hε)

theorem smallGradient_curve_image_integral_bound {d : ℕ} (p : AmbientPolynomial d)
    {γ v : ℝ → TorusAmbient d} {R ε : ℝ} (hR : 0 ≤ R)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt γ (v t) (Set.Icc 0 1) t)
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ smallGradientSphere (torusPartial p) R ε)
    (hv : ContinuousOn v (Set.Icc (0 : ℝ) 1)) :
    ‖ambientEval p (R • γ 1) - ambientEval p (R • γ 0)‖ ≤
      ε * ∫ t in (0 : ℝ)..1, ‖v t‖ := by
  have hc : ContinuousOn γ (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hγ t ht).continuousWithinAt
  let F' (t : ℝ) := polynomialDifferential p (R • γ t) (R • v t)
  have hF : ContinuousOn F' (Set.Icc (0 : ℝ) 1) := by
    simp only [F', polynomialDifferential_apply]
    apply continuousOn_finsetSum
    intro i _
    exact ((ambientEval_continuous _).comp_continuousOn (hc.const_smul R)).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d => ℂ) i).comp_continuousOn (hv.const_smul R))
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    smallGradient_curve_hasDerivWithinAt p (R := R) (hγ t ht)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (hF.intervalIntegrable_of_Icc zero_le_one)
  rw [← heq]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖F' t‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, ε * ‖v t‖ := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hF.norm.intervalIntegrable_of_Icc zero_le_one)
        ((continuousOn_const.mul hv.norm).intervalIntegrable_of_Icc zero_le_one)
      intro t ht
      exact smallGradient_curve_derivative_norm_le p ht
        (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht) hR (hγ t ht) hX
    _ = ε * ∫ t in (0 : ℝ)..1, ‖v t‖ := intervalIntegral.integral_const_mul ε _

end
end DuistermaatVanDerKallen
