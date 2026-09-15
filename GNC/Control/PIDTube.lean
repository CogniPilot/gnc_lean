import GNC.Control.ReferenceTube

/-! A PID example with the integrator and rate state retained.

This is an acceleration-level PID with gains (kI,kP,kD)=(1,3,3), in
dimensionless error variables. r is the exact kinematic residual and d the
exact acceleration residual, including any failure to realize the requested
acceleration. These residuals are not set to zero for a physical aircraft.
The certificate is explicit and needs no numerical LMI solver.
-/
noncomputable section
open Set Real
namespace GNC.PIDTube
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def storage (η q v : E) : ℝ :=
  ‖η‖^2+2*‖η+q‖^2+4*‖η+2 • q+v‖^2

theorem storage_nonneg (η q v : E) : 0 ≤ storage η q v := by
  unfold storage
  positivity

theorem storage_eq_zero_iff (η q v : E) : storage η q v = 0 ↔ η=0 ∧ q=0 ∧ v=0 := by
  constructor
  · intro h
    have hη : ‖η‖^2=0 := by
      dsimp [storage] at h
      nlinarith [sq_nonneg ‖η+q‖,sq_nonneg ‖η+2 • q+v‖]
    have he : η=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hη)
    subst η
    simp only [storage, zero_add, norm_zero, zero_pow (by decide : 2≠0),
      zero_add] at h
    have hq : ‖q‖^2=0 := by nlinarith [sq_nonneg ‖2 • q+v‖]
    have he : q=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hq)
    subst q
    simpa using h
  · rintro ⟨rfl,rfl,rfl⟩
    simp [storage]

/-- The PID error chain has a triangular representation, while retaining
both the nonlinear kinematic residual and the acceleration disturbance. -/
theorem storage_derivative {η q v : ℝ → E} {r d : E} {t : ℝ}
    (hη : HasDerivAt η (q t) t)
    (hq : HasDerivAt q (v t+r) t)
    (hv : HasDerivAt v (-η t-3 • q t-3 • v t+d) t) :
    HasDerivAt (fun s => storage (η s) (q s) (v s))
      (2*inner ℝ (η t) (-η t+(η t+q t))+
       4*inner ℝ (η t+q t) (-(η t+q t)+(η t+2 • q t+v t)+r)+
       8*inner ℝ (η t+2 • q t+v t) (-(η t+2 • q t+v t)+2 • r+d)) t := by
  have h₂ : HasDerivAt (fun s => η s+q s)
      (-(η t+q t)+(η t+2 • q t+v t)+r) t := by
    convert hη.add hq using 1 <;> module
  have h₃ : HasDerivAt (fun s => η s+2 • q s+v s)
      (-(η t+2 • q t+v t)+2 • r+d) t := by
    convert (hη.add (hq.const_smul 2)).add hv using 1 <;> module
  convert (hη.norm_sq.add (h₂.norm_sq.const_mul 2)).add
    (h₃.norm_sq.const_mul 4) using 1
  simp only [neg_add_cancel_left]
  ring

/-- Exact quadratic supply for all error states. Residuals are kept as
separate channels: no claim that a PID cancels Lie-Jacobian nonlinearities. -/
theorem supply (x y z r d : E) :
    2*inner ℝ x (-x+y)+4*inner ℝ y (-y+z+r)+
      8*inner ℝ z (-z+2 • r+d)+(1/4 : ℝ)*(‖x‖^2+2*‖y‖^2+4*‖z‖^2) ≤
      72*‖r‖^2+8*‖d‖^2 := by
  have hxy := Lyapunov.inner_young x y (by norm_num : (0:ℝ)<1)
  have hyz := Lyapunov.inner_young y z (by norm_num : (0:ℝ)<1)
  have hyr := Lyapunov.inner_young y r (by norm_num : (0:ℝ)<1/4)
  have hzr := Lyapunov.inner_young z r (by norm_num : (0:ℝ)<1/8)
  have hzd := Lyapunov.inner_young z d (by norm_num : (0:ℝ)<1/2)
  simp only [two_smul, inner_add_right, inner_neg_right,
    real_inner_self_eq_norm_sq]
  norm_num at hxy hyz hyr hzr hzd
  nlinarith [sq_nonneg ‖x‖,sq_nonneg ‖z‖]

/-- A regionally bounded residual gives a reference-error tube for the
complete PID state. The boundary premise is enough: there is no assumption
that the actual trajectory has already stayed in the candidate tube. -/
theorem invariant_tube {η q v : ℝ → E} {r d : ℝ → E}
    {ρ dρ residualBudget accelerationBudget reserve : ℝ → ℝ} {a b : ℝ}
    (hη : ∀ s ∈ Icc a b, HasDerivAt η (q s) s)
    (hq : ∀ s ∈ Icc a b, HasDerivAt q (v s+r s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-η s-3 • q s-3 • v s+d s) s)
    (hρ : ∀ s, HasDerivAt ρ (dρ s) s)
    (hinit : storage (η a) (q a) (v a) ≤ ρ a)
    (hr : ∀ s ∈ Ico a b, storage (η s) (q s) (v s) ≤ ρ s →
      ‖r s‖^2 ≤ residualBudget s)
    (hd : ∀ s ∈ Ico a b, storage (η s) (q s) (v s) ≤ ρ s →
      ‖d s‖^2 ≤ accelerationBudget s)
    (hreserve : ∀ s ∈ Ico a b, 0 < reserve s)
    (hradius : ∀ s ∈ Ico a b,
      72*residualBudget s+8*accelerationBudget s+reserve s ≤ dρ s+ρ s/4) :
    ∀ t ∈ Icc a b, storage (η t) (q t) (v t) ≤ ρ t := by
  have hder := fun s hs => storage_derivative (hη s hs) (hq s hs) (hv s hs)
  apply image_le_of_deriv_right_lt_deriv_boundary
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt) hinit hρ
  intro s hs he
  have h := supply (η s) (η s+q s) (η s+2 • q s+v s) (r s) (d s)
  change _ + (1/4 : ℝ)*storage (η s) (q s) (v s) ≤ _ at h
  rw [he] at h
  have h₁ := hr s hs he.le
  have h₂ := hd s hs he.le
  have h₃ := hradius s hs
  have h₄ := hreserve s hs
  linarith

end GNC.PIDTube
