import DuistermaatVanDerKallen.LaurentTransport

/-! Chosen segment trajectories and the induced fiber transport maps.
Uniqueness removes dependence on the chosen existence witnesses. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- A fiber in the original nonvanishing-coordinate torus. -/
abbrev LaurentFiber {d : ℕ} (f : MultiLaurent d) (s : ℂ) :=
  {z : Fin d → ℂ // (∀ i, z i ≠ 0) ∧ laurentEval f z = s}

/-- Precisely the exclusion hypothesis for a base segment. -/
def GoodSegment {d : ℕ} (f : MultiLaurent d) (s a : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, s + t • a ∉
    ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f)

theorem GoodSegment.reverse {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : GoodSegment f (s + a) (-a) := by
  intro t ht
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have heq : s + a + t • (-a) = s + (1 - t) • a := by
    simp [sub_smul, smul_neg]
    abel
  rw [heq]
  exact h (1 - t) ht'

/-- Complete existence specialized to a fiber, retaining endpoints. -/
theorem fiber_curve_exists {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) :
    ∃ γ : ℝ → (Fin d → ℂ), γ 0 = z.val ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f a (γ t)) t ∧ laurentEval f (γ t) = s + t • a := by
  obtain ⟨δ, hδ, b, hb, γ, hγ, hd⟩ := laurent_complete_segment f z.val z.property.1 a
    (by intro t ht; rw [z.property.2]; exact h t ht)
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hti : t ∈ Ioo (-δ) b := by constructor <;> linarith [ht.1, ht.2]
  simpa [z.property.2] using hd t hti

/-- A choice of complete trajectory, unique on the unit time interval. -/
def fiberCurve {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) : ℝ → (Fin d → ℂ) :=
  (fiber_curve_exists h z).choose

theorem fiberCurve_spec {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) :
    fiberCurve h z 0 = z.val ∧
      ∀ t ∈ Icc (0 : ℝ) 1, fiberCurve h z t ∈ laurentRegularDomain f ∧
        HasDerivAt (fiberCurve h z) (laurentVectorField f a (fiberCurve h z t)) t ∧
        laurentEval f (fiberCurve h z t) = s + t • a :=
  (fiber_curve_exists h z).choose_spec

/-- Time-one transport into the endpoint fiber. -/
def fiberTransport {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) : LaurentFiber f (s + a) :=
  ⟨fiberCurve h z 1, ((fiberCurve_spec h z).2 1 (by simp)).1.1,
    by simpa using ((fiberCurve_spec h z).2 1 (by simp)).2.2⟩

/-- Transport along the reversed segment, with the endpoint type simplified. -/
def fiberTransportBack {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f (s + a)) : LaurentFiber f s :=
  ⟨fiberCurve h.reverse z 1, ((fiberCurve_spec h.reverse z).2 1 (by simp)).1.1,
    by simpa using ((fiberCurve_spec h.reverse z).2 1 (by simp)).2.2⟩

/-- Reversing transport returns every starting point. -/
theorem fiberTransport_left_inv {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f s) :
    fiberTransportBack h (fiberTransport h z) = z := by
  apply Subtype.ext
  have hrev := laurent_segment_reverse_inverse f a
    (fun t ht => ⟨((fiberCurve_spec h z).2 t ht).1, ((fiberCurve_spec h z).2 t ht).2.1⟩)
    (fun t ht => ⟨((fiberCurve_spec h.reverse (fiberTransport h z)).2 t ht).1,
      ((fiberCurve_spec h.reverse (fiberTransport h z)).2 t ht).2.1⟩)
    ((fiberCurve_spec h.reverse (fiberTransport h z)).1)
  simpa [fiberTransportBack, (fiberCurve_spec h z).1] using hrev (by simp : (1 : ℝ) ∈ Icc 0 1)

/-- Forward transport is also inverse to reversed transport. -/
theorem fiberTransport_right_inv {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) (z : LaurentFiber f (s + a)) :
    fiberTransport h (fiberTransportBack h z) = z := by
  apply Subtype.ext
  have hfwd : ∀ t ∈ Icc (0 : ℝ) 1,
      fiberCurve h (fiberTransportBack h z) t ∈ laurentRegularDomain f ∧
      HasDerivAt (fiberCurve h (fiberTransportBack h z))
        (laurentVectorField f (-(-a)) (fiberCurve h (fiberTransportBack h z) t)) t := by
    intro t ht
    simpa using ⟨((fiberCurve_spec h (fiberTransportBack h z)).2 t ht).1,
      ((fiberCurve_spec h (fiberTransportBack h z)).2 t ht).2.1⟩
  have hrev := laurent_segment_reverse_inverse f (-a)
    (fun t ht => ⟨((fiberCurve_spec h.reverse z).2 t ht).1,
      ((fiberCurve_spec h.reverse z).2 t ht).2.1⟩) hfwd
    ((fiberCurve_spec h (fiberTransportBack h z)).1)
  simpa [fiberTransport, (fiberCurve_spec h.reverse z).1] using
    hrev (by simp : (1 : ℝ) ∈ Icc 0 1)

/-- The underlying bijection supplied by segment transport.
Topology and smoothness are proved separately; neither is part of this definition. -/
def fiberTransportEquiv {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : LaurentFiber f s ≃ LaurentFiber f (s + a) where
  toFun := fiberTransport h
  invFun := fiberTransportBack h
  left_inv := fiberTransport_left_inv h
  right_inv := fiberTransport_right_inv h

/-- Regression: a stationary base segment induces the identity on fiber points. -/
theorem fiberTransport_zero {d : ℕ} {f : MultiLaurent d} {s : ℂ}
    (h : GoodSegment f s 0) (z : LaurentFiber f s) :
    (fiberTransport h z).val = z.val := by
  have hz : z.val ∈ laurentRegularDomain f := by
    simpa only [(fiberCurve_spec h z).1] using ((fiberCurve_spec h z).2 0 (by simp)).1
  have heq := laurent_segment_unique f 0
    (fun t ht => ⟨((fiberCurve_spec h z).2 t ht).1, ((fiberCurve_spec h z).2 t ht).2.1⟩)
    (fun t _ => laurent_zero_velocity_curve f hz t) (fiberCurve_spec h z).1
  exact heq (by simp : (1 : ℝ) ∈ Icc 0 1)

end
end DuistermaatVanDerKallen
