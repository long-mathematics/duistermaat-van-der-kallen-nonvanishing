import DuistermaatVanDerKallen.C1FiberTransport

/-! Endpoint transport for finite composable chains of regular C¹ base pieces.
No differentiability across a corner is required or claimed. -/

open scoped Manifold

namespace DuistermaatVanDerKallen
noncomputable section

/-- A finite nonempty sequence of C¹ pieces with matching base endpoints. -/
inductive LaurentC1Chain {d : ℕ} (f : MultiLaurent d) : ℂ → ℂ → Type
  | single {s t : ℂ} : LaurentC1Path f s t → LaurentC1Chain f s t
  | append {s t u : ℂ} : LaurentC1Chain f s t → LaurentC1Path f t u → LaurentC1Chain f s u

namespace LaurentC1Chain
variable {d : ℕ} {f : MultiLaurent d} {s t : ℂ}

theorem start_regular (h : LaurentC1Chain f s t) : RegularLaurentValue f s := by
  induction h with
  | single h => exact h.start_regular
  | append _ _ ih => exact ih

theorem end_regular (h : LaurentC1Chain f s t) : RegularLaurentValue f t := by
  cases h with
  | single h => exact h.end_regular
  | append _ h => exact h.end_regular

/-- Compose the actual endpoint maps of the individual driven trajectories. -/
def transport : {s t : ℂ} → LaurentC1Chain f s t → LaurentFiber f s → LaurentFiber f t
  | _, _, .single h => h.transport
  | _, _, .append h k => k.transport ∘ h.transport

/-- Invert each piece and traverse the pieces in reverse order. -/
def transportBack : {s t : ℂ} → LaurentC1Chain f s t → LaurentFiber f t → LaurentFiber f s
  | _, _, .single h => h.reverse.transport
  | _, _, .append h k => h.transportBack ∘ k.reverse.transport

@[simp] theorem transport_left_inv (h : LaurentC1Chain f s t) (z : LaurentFiber f s) :
    h.transportBack (h.transport z) = z := by
  induction h generalizing z with
  | single h => simpa only [transport, transportBack] using h.transport_left_inv z
  | append h k ih => simpa only [transport, transportBack, Function.comp_apply, k.transport_left_inv] using ih z

@[simp] theorem transport_right_inv (h : LaurentC1Chain f s t) (z : LaurentFiber f t) :
    h.transport (h.transportBack z) = z := by
  induction h with
  | single h => simpa only [transport, transportBack] using h.transport_right_inv z
  | append h k ih => simp only [transport, transportBack, Function.comp_apply, ih, k.transport_right_inv]

def transportEquiv (h : LaurentC1Chain f s t) : LaurentFiber f s ≃ LaurentFiber f t where
  toFun := h.transport
  invFun := h.transportBack
  left_inv := h.transport_left_inv
  right_inv := h.transport_right_inv

/-- Analytic dependence on initial data survives finite composition. -/
theorem transport_contMDiff (h : LaurentC1Chain f s t)
    [hS : Fact (RegularLaurentValue f s)] [hT : Fact (RegularLaurentValue f t)] :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ h.transport := by
  revert hS hT
  induction h with
  | single h =>
    intro hS hT
    simpa only [transport] using h.transport_contMDiff
  | append h k ih =>
    intro hS hT
    let : Fact (RegularLaurentValue f _) := ⟨k.start_regular⟩
    simpa only [transport] using k.transport_contMDiff.comp ih

theorem transportBack_contMDiff (h : LaurentC1Chain f s t)
    [hS : Fact (RegularLaurentValue f s)] [hT : Fact (RegularLaurentValue f t)] :
    ContMDiff (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) ⊤ h.transportBack := by
  revert hS hT
  induction h with
  | single h =>
    intro hS hT
    simpa only [transportBack] using h.reverse.transport_contMDiff
  | append h k ih =>
    intro hS hT
    let : Fact (RegularLaurentValue f _) := ⟨k.start_regular⟩
    simpa only [transportBack] using ih.comp k.reverse.transport_contMDiff

/-- Complete endpoint transport for any finite chain of regular C¹ pieces. -/
def transportDiffeomorph (h : LaurentC1Chain f s t) :
    letI : Fact (RegularLaurentValue f s) := ⟨h.start_regular⟩
    letI : Fact (RegularLaurentValue f t) := ⟨h.end_regular⟩
    Diffeomorph (modelWithCornersSelf ℝ (LaurentFiberModel d))
      (modelWithCornersSelf ℝ (LaurentFiberModel d)) (LaurentFiber f s) (LaurentFiber f t) ⊤ := by
  letI : Fact (RegularLaurentValue f s) := ⟨h.start_regular⟩
  letI : Fact (RegularLaurentValue f t) := ⟨h.end_regular⟩
  exact { toEquiv := h.transportEquiv
          contMDiff_toFun := h.transport_contMDiff
          contMDiff_invFun := h.transportBack_contMDiff }

end LaurentC1Chain
end
end DuistermaatVanDerKallen
