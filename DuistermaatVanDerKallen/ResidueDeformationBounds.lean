import DuistermaatVanDerKallen.ResidueDeformation

/-! Uniform bounds for the first-coordinate deformation on the closed unit
parameter disc. The constants do not depend on the base circles or on the deformation parameter. -/

namespace DuistermaatVanDerKallen
noncomputable section

structure ResidueDiscData {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (u : MvPolynomial (Fin (d + 1)) ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  unit : ∀ y : Fin (d + 1) → ℂ, (∀ i, ‖y i‖ ≤ radius) → MvPolynomial.eval y u ≠ 0
  eval_bound : ∀ y : Fin (d + 1) → ℂ, (∀ i, ‖y i‖ ≤ radius) → ‖MvPolynomial.eval y u‖ ≤ bound
  partial_bound : ∀ y : Fin (d + 1) → ℂ, (∀ i, ‖y i‖ ≤ radius) →
    ‖y 0 * MvPolynomial.eval y (MvPolynomial.pderiv 0 u)‖ < (m 0 : ℝ) * ‖MvPolynomial.eval y u‖

theorem nonempty_residueDiscData {d : ℕ} (m : Fin (d + 1) →₀ ℕ)
    (hm : ∀ i, 0 < m i) (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    Nonempty (ResidueDiscData m u) := by
  obtain ⟨ε, hε, hdisc⟩ := exists_polynomial_derivative_polydisc u hu
    (fun i => (m i : ℝ)) (fun i => by exact_mod_cast hm i)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin (d + 1) → ℂ) ε).exists_bound_of_continuousOn
    (MvPolynomial.continuous_eval u).continuousOn
  refine ⟨⟨ε, hε, max C 0, le_max_right _ _, fun y hy => (hdisc y hy).1, ?_,
    fun y hy => (hdisc y hy).2 0⟩⟩
  intro y hy
  apply (hC y ?_).trans (le_max_left _ _)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg hε.le).mpr hy

namespace ResidueDiscData
variable {d : ℕ} {m : Fin (d + 1) →₀ ℕ} {u : MvPolynomial (Fin (d + 1)) ℂ}
variable (D : ResidueDiscData m u)

def monomialRadius : ℝ := ∏ i, D.radius ^ m i

theorem monomialRadius_pos : 0 < D.monomialRadius :=
  Finset.prod_pos (fun _ _ => pow_pos D.radius_pos _)

def threshold : ℝ := max 1 (D.bound / D.monomialRadius)

theorem leading_bound {s : ℂ} (hs : D.threshold < ‖s‖) :
    D.bound < ‖s‖ * D.monomialRadius :=
  (div_lt_iff₀ D.monomialRadius_pos).mp ((le_max_right _ _).trans_lt hs)

theorem fiberValue_ne_zero {s : ℂ} (hs : D.threshold < ‖s‖) : s ≠ 0 :=
  norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 1) ((le_max_left _ _).trans_lt hs))

theorem scaled_cons_mem_disc {t z : ℂ} {b : Fin d → ℂ}
    (ht : ‖t‖ ≤ 1) (hz : ‖z‖ ≤ D.radius) (hb : ∀ i, ‖b i‖ = D.radius) :
    ∀ i : Fin (d + 1), ‖(Fin.cons (t * z) b : Fin (d + 1) → ℂ) i‖ ≤ D.radius := by
  intro i
  refine Fin.cases ?_ (fun j => (hb j).le) i
  simp only [Fin.cons_zero, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht).trans hz

theorem monomial_norm_on_boundary (s : ℂ) {z : ℂ} {b : Fin d → ℂ}
    (hz : ‖z‖ = D.radius) (hb : ∀ i, ‖b i‖ = D.radius) :
    ‖MvPolynomial.eval (Fin.cons z b) (MvPolynomial.monomial m s)‖ =
      ‖s‖ * D.monomialRadius := by
  classical
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype, pow_zero, implies_true,
    norm_mul, norm_prod, norm_pow, monomialRadius]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hz]
  · simp [hb]

theorem deformation_boundary_ne_zero {s : ℂ} (hs : D.threshold < ‖s‖)
    {t z : ℂ} {b : Fin d → ℂ} (ht : ‖t‖ ≤ 1)
    (hz : ‖z‖ = D.radius) (hb : ∀ i, ‖b i‖ = D.radius) :
    residueDeformationEquation m u s ((t, b), z) ≠ 0 := by
  intro he
  have heq : MvPolynomial.eval (Fin.cons z b) (MvPolynomial.monomial m s) =
      MvPolynomial.eval (Fin.cons (t * z) b) u := sub_eq_zero.mp he
  have hn := congrArg norm heq
  rw [D.monomial_norm_on_boundary s hz hb] at hn
  have hU := D.eval_bound _ (D.scaled_cons_mem_disc ht hz.le hb)
  exact (not_lt_of_ge hU) (hn ▸ D.leading_bound hs)

theorem deformation_regular_root {s : ℂ} (hs : D.threshold < ‖s‖)
    {t z : ℂ} {b : Fin d → ℂ} (ht : ‖t‖ ≤ 1)
    (hz : ‖z‖ ≤ D.radius) (hb : ∀ i, ‖b i‖ = D.radius)
    (hroot : residueDeformationEquation m u s ((t, b), z) = 0) :
    z ≠ 0 ∧ ‖z‖ < D.radius ∧
      deriv (fun w => residueDeformationEquation m u s ((t, b), w)) z ≠ 0 := by
  have hbnd := D.partial_bound _ (D.scaled_cons_mem_disc ht hz hb)
  obtain ⟨hnz, hd⟩ := residueDeformationEquation_regular_root m u s t z b hroot hbnd
  refine ⟨hnz, lt_of_le_of_ne hz ?_, hd⟩
  intro he
  exact D.deformation_boundary_ne_zero hs ht he hb hroot

end ResidueDiscData
end
end DuistermaatVanDerKallen
