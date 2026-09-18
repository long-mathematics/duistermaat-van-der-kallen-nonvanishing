import DuistermaatVanDerKallen.SeparableRelation
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Smoothness of continuous algebraic root selections outside a finite
exceptional set. Simple-root relations come from `SeparableRelation`;
the ordinary real implicit-function theorem then identifies the given
continuous selection with a smooth local branch. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Polynomial Filter
open scoped Topology

def bivariateEval (P : Polynomial (Polynomial ℝ)) (q : ℝ × ℝ) : ℝ :=
  (P.map (Polynomial.evalRingHom q.1)).eval q.2

theorem bivariateEval_contDiff (P : Polynomial (Polynomial ℝ)) :
    ContDiff ℝ ⊤ (bivariateEval P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    funext q
    simp [bivariateEval]
  | monomial n a =>
    have ha : ContDiff ℝ ⊤ (fun q : ℝ × ℝ => a.eval q.1) := by
      have hc : ContDiff ℝ ⊤ (fun t : ℝ => a.eval t) := by
        convert a.contDiff_aeval (𝕜 := ℝ) ⊤ using 1
        funext t
        simp
      exact hc.comp contDiff_fst
    convert ha.mul (contDiff_snd.pow n) using 1
    funext q
    simp [bivariateEval]

theorem realLinearMap_isInvertible {L : ℝ →L[ℝ] ℝ} (hL : L 1 ≠ 0) : L.IsInvertible := by
  have he (a : ℝ) : L a = a * L 1 := by simpa using L.map_smul a (1 : ℝ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext
    intro a
    change L ((L 1)⁻¹ * a) = a
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro a
    change (L 1)⁻¹ * L a = a
    rw [he a]
    field_simp

theorem bivariateEval_partial_isInvertible (P : Polynomial (Polynomial ℝ)) (q : ℝ × ℝ)
    (hq : ((P.map (Polynomial.evalRingHom q.1)).derivative).eval q.2 ≠ 0) :
    (fderiv ℝ (bivariateEval P) q ∘L .inr ℝ ℝ ℝ).IsInvertible := by
  apply realLinearMap_isInvertible
  have hd := (((bivariateEval_contDiff P).differentiable (by simp)).differentiableAt
    (x := q)).hasFDerivAt
  have hg : HasDerivAt (fun z : ℝ => (q.1, z)) (0, 1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have he := (hd.comp_hasDerivAt q.2 hg).deriv
  have hp := ((P.map (Polynomial.evalRingHom q.1)).hasDerivAt q.2).deriv
  change fderiv ℝ (bivariateEval P) q (0, 1) ≠ 0
  rw [← he]
  exact hp ▸ hq

theorem contDiffAt_of_continuous_algebraic_simple_root
    (P : Polynomial (Polynomial ℝ)) (f : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x)
    (hroot : ∀ᶠ t in 𝓝 x, bivariateEval P (t, f t) = 0)
    (hder : ((P.map (Polynomial.evalRingHom x)).derivative).eval (f x) ≠ 0) :
    ContDiffAt ℝ ⊤ f x := by
  have hc := (bivariateEval_contDiff P).contDiffAt (x := (x, f x))
  have hi := bivariateEval_partial_isInvertible P (x, f x) hder
  have he := hc.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have ht : Tendsto (fun t => (t, f t)) (𝓝 x) (𝓝 (x, f x)) :=
    continuousAt_id.prodMk hf
  have hzero : bivariateEval P (x, f x) = 0 := hroot.self_of_nhds
  have heq : f =ᶠ[𝓝 x] hc.implicitFunction (by simp) hi := by
    filter_upwards [ht.eventually he, hroot] with t ht hr
    exact (ht.mp (hr.trans hzero.symm)).symm
  exact (hc.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq heq

theorem continuous_algebraic_smooth_outside_finite
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    (f : ℝ → ℝ) (S : Set ℝ) (hS : IsOpen S) (hf : ContinuousOn f S)
    (hroot : ∀ x ∈ S, bivariateEval P (x, f x) = 0) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x ∈ S, x ∉ E → ContDiffAt ℝ ⊤ f x := by
  obtain ⟨Q, _, E, hE, hQ⟩ := polynomial_simple_relation_outside_finite P hP
  refine ⟨E, hE, ?_⟩
  intro x hx hxE
  apply contDiffAt_of_continuous_algebraic_simple_root Q f x
    ((hf x hx).continuousAt (hS.mem_nhds hx))
  · have he : Eᶜ ∈ 𝓝 x := hE.isClosed.isOpen_compl.mem_nhds hxE
    filter_upwards [hS.mem_nhds hx, he] with t ht htE
    exact (hQ t htE (f t) (hroot t ht)).1
  · exact (hQ x hxE (f x) (hroot x hx)).2

end
end DuistermaatVanDerKallen
