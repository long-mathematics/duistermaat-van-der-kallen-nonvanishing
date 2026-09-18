import DuistermaatVanDerKallen.SpherePathChain
import DuistermaatVanDerKallen.AffineSemialgebraic
import DuistermaatVanDerKallen.UniformGradient

/-! The actual critical locus and constancy along finite C1 chains. -/

namespace DuistermaatVanDerKallen
noncomputable section

theorem ambientDifferentialNorm_eq_zero_iff {d : ℕ} (g : Fin d → AmbientPolynomial d)
    (x : TorusAmbient d) :
    ambientDifferentialNorm g x = 0 ↔ ∀ i, ambientEval (g i) x = 0 := by
  have hb (i : Fin d) : 0 < (1 : ℝ) + ‖x (.inr i)‖ ^ 4 := by positivity
  have hn (i : Fin d) : 0 ≤ Complex.normSq (ambientEval (g i) x) /
      (1 + ‖x (.inr i)‖ ^ 4) := div_nonneg (Complex.normSq_nonneg _) (hb i).le
  unfold ambientDifferentialNorm differentialNormSq
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun i _ => hn i)),
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro i
  simp [div_eq_zero_iff, ne_of_gt (hb i)]

def criticalTorusLocus {d : ℕ} (p : AmbientPolynomial d) : Set (TorusAmbient d) :=
  {x | x ∈ affineTorus d ∧ ambientDifferentialNorm (torusPartial p) x = 0}

theorem isComplexSemialgebraic_criticalTorusLocus {d : ℕ} (p : AmbientPolynomial d) :
    IsComplexSemialgebraic {x : (Fin d ⊕ Fin d) → ℂ |
      WithLp.toLp 2 x ∈ criticalTorusLocus p} := by
  have h := (isComplexSemialgebraic_affineTorus d).inter
    (isComplexSemialgebraic_ambientDifferentialNorm_le (torusPartial p) (le_refl 0))
  convert h using 1
  ext x
  simp only [criticalTorusLocus, Set.mem_ofPred_eq, Set.mem_inter_iff]
  apply and_congr_right
  intro _
  exact ⟨fun h => h.le, fun h => le_antisymm h (Real.sqrt_nonneg _)⟩

theorem critical_curve_image_eq {d : ℕ} (p : AmbientPolynomial d)
    {γ v : ℝ → TorusAmbient d}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt γ (v t) (Set.Icc 0 1) t)
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ criticalTorusLocus p) :
    ambientEval p (γ 1) = ambientEval p (γ 0) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s => ambientEval p (γ s))
        (polynomialDifferential p (γ t) (v t)) (Set.Icc 0 1) t := by
    simpa only [one_smul] using smallGradient_curve_hasDerivWithinAt p (R := 1) (hγ t ht)
  have hb : ‖ambientEval p (γ 1) - ambientEval p (γ 0)‖ ≤ 0 := by
    apply norm_image_sub_le_of_norm_deriv_le_segment_01' hd
    intro t ht
    have ht' := Set.Ico_subset_Icc_self ht
    have hv := curve_derivative_mem_torusTangentSpace ht'
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht') (hγ t ht')
      (fun s hs => (hX s hs).1)
    have h := polynomialDifferential_norm_le_on_tangent p (hX t ht').1 hv
    simpa only [(hX t ht').2, zero_mul] using h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

theorem C1ArcChain.critical_image_eq {d : ℕ} (p : AmbientPolynomial d)
    {x y : TorusAmbient d} (γ : C1ArcChain (criticalTorusLocus p) x y) :
    ambientEval p x = ambientEval p y := by
  have h : dist (ambientEval p (γ.node 0)) (ambientEval p (γ.node γ.pieces)) ≤ 0 := by
    have hbound := dist_le_range_sum_of_dist_le (f := fun i => ambientEval p (γ.node i))
      γ.pieces (d := fun _ => 0) (fun {i} hi => ?_)
    · simpa using hbound
    · have he := critical_curve_image_eq p (γ.derivative i hi) (γ.curve_mem i hi)
      rw [γ.start i hi, γ.finish i hi] at he
      simp only [he, dist_self, le_refl]
  exact dist_eq_zero.mp (le_antisymm (by simpa only [γ.source, γ.target] using h) dist_nonneg)

theorem ordinaryCriticalValues_eq_criticalTorusLocus_range {d : ℕ} (p : AmbientPolynomial d) :
    ordinaryCriticalValues (fun x : affineTorus d => ambientEval p x.val)
      (fun x => ambientDifferentialNorm (torusPartial p) x.val) =
      Set.range (fun x : criticalTorusLocus p => ambientEval p x.val) := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, x.property, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, x.property.1⟩, x.property.2, rfl⟩

end
end DuistermaatVanDerKallen
