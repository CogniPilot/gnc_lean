import GNC.Analysis.ForcedProductConvolution

/-! Remove exactly vanishing low-order terms before a modal sum.
The spectral resolution is explicit. The cancellation is shared by any
Cartesian implementation using the same acceleration/position structure.
No eigenvalue separation or small-time tolerance is required.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.QuadraticModalCancellation
open scoped BigOperators

variable {E F I : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [Fintype I]

def weighted (rates : I → ℂ) (P : I → E →ₗ[ℂ] E) (b : E) (n : ℕ) : E :=
  ∑ i, rates i^n • P i b

theorem weighted_power (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hidentity : ∀ b, ∑ i, P i b = b)
    (heigen : ∀ i b, A (P i b) = rates i • P i b) (b : E) (n : ℕ) :
    weighted rates P b n = (A^n) b := by
  induction n with
  | zero => simp [weighted, hidentity]
  | succ n ih =>
    calc
      _ = A (weighted rates P b n) := by
        simp only [weighted, map_sum, map_smul, heigen, smul_smul, pow_succ]
      _ = (A^(n+1)) b := by rw [ih, pow_succ']; rfl

def responseSum (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (f : ℂ → ℂ → ℂ → ℂ) : F :=
  ∑ i, ∑ j, ∑ k, f (rates i) (rates j) (rates k) • C (P i (B (P j b) (P k b)))

/-- Finite modal power moments reassemble into actual operator powers. -/
theorem power_moment (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hidentity : ∀ b, ∑ i, P i b = b)
    (heigen : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E) (p q r : ℕ) :
    responseSum rates P B C b (fun x y z => x^p*y^q*z^r) =
      C ((A^p) (B ((A^q) b) ((A^r) b))) := by
  rw [← weighted_power A rates P hidentity heigen b q,
    ← weighted_power A rates P hidentity heigen b r,
    ← weighted_power A rates P hidentity heigen _ p]
  simp only [weighted, responseSum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

theorem responseSum_add (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (f g : ℂ → ℂ → ℂ → ℂ) :
    responseSum rates P B C b (fun x y z => f x y z+g x y z) =
      responseSum rates P B C b f+responseSum rates P B C b g := by
  simp [responseSum, add_smul, Finset.sum_add_distrib]

theorem responseSum_sub (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (f g : ℂ → ℂ → ℂ → ℂ) :
    responseSum rates P B C b (fun x y z => f x y z-g x y z) =
      responseSum rates P B C b f-responseSum rates P B C b g := by
  simp [responseSum, sub_smul, Finset.sum_sub_distrib]

theorem responseSum_scale (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (d : ℂ) (f : ℂ → ℂ → ℂ → ℂ) :
    responseSum rates P B C b (fun x y z => d*f x y z) =
      d • responseSum rates P B C b f := by
  simp [responseSum, mul_smul, Finset.smul_sum]

def c3 (x y z : ℂ) : ℂ := (1/3:ℂ)*(x^0*y^0*z^0)
def c4 (x y z : ℂ) : ℂ :=
  (1/12:ℂ)*(x^1*y^0*z^0)+(1/8:ℂ)*(x^0*y^1*z^0)+(1/8:ℂ)*(x^0*y^0*z^1)
def c5 (x y z : ℂ) : ℂ :=
  (1/60:ℂ)*(x^2*y^0*z^0)+(1/40:ℂ)*(x^1*y^1*z^0)+
  (1/40:ℂ)*(x^1*y^0*z^1)+(1/30:ℂ)*(x^0*y^2*z^0)+
  (1/30:ℂ)*(x^0*y^0*z^2)+(1/20:ℂ)*(x^0*y^1*z^1)

theorem coefficient_recursion (x y z : ℂ) :
    3*c3 x y z = 1 ∧
    4*c4 x y z = x*c3 x y z+(y+z)/2 ∧
    5*c5 x y z = x*c4 x y z+(y^2+z^2)/6+y*z/4 := by
  simp only [c3, c4, c5, pow_zero, pow_one]
  constructor
  · ring
  constructor <;> ring

theorem cancel_c3 (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (hb : ∀ x, B b x = 0) : responseSum rates P B C b c3 = 0 := by
  unfold c3
  rw [responseSum_scale, power_moment A rates P hi he]
  simp [hb]

theorem cancel_c4 (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (hl : ∀ x, B b x = 0) (hr : ∀ x, B x b = 0) :
    responseSum rates P B C b c4 = 0 := by
  unfold c4
  simp only [responseSum_add, responseSum_scale, power_moment A rates P hi he]
  simp [hl, hr]

theorem cancel_c5_position (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (hl : ∀ x, B b x = 0) (hr : ∀ x, B x b = 0)
    (hC : ∀ x y, C (B x y) = 0) : responseSum rates P B C b c5 = 0 := by
  unfold c5
  simp only [responseSum_add, responseSum_scale, power_moment A rates P hi he]
  simp [hl, hr, hC]

/-- Any scalar kernel may have these polynomials subtracted before summing.
This is an exact equality, not a small-time approximation. -/
theorem subtract_position_terms (A : E →ₗ[ℂ] E) (rates : I → ℂ)
    (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (hl : ∀ x, B b x = 0) (hr : ∀ x, B x b = 0)
    (hC : ∀ x y, C (B x y) = 0) (K : ℂ → ℂ → ℂ → ℂ) (t : ℂ) :
    responseSum rates P B C b (fun x y z =>
      K x y z-(t^3*c3 x y z+t^4*c4 x y z+t^5*c5 x y z)) =
      responseSum rates P B C b K := by
  rw [responseSum_sub]
  simp only [responseSum_add, responseSum_scale,
    cancel_c3 A rates P hi he B C b hl, cancel_c4 A rates P hi he B C b hl hr,
    cancel_c5_position A rates P hi he B C b hl hr hC, smul_zero, add_zero, sub_zero]

theorem subtract_velocity_terms (A : E →ₗ[ℂ] E) (rates : I → ℂ)
    (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (hl : ∀ x, B b x = 0) (hr : ∀ x, B x b = 0)
    (K : ℂ → ℂ → ℂ → ℂ) (t : ℂ) :
    responseSum rates P B C b (fun x y z => K x y z-(t^3*c3 x y z+t^4*c4 x y z)) =
      responseSum rates P B C b K := by
  rw [responseSum_sub]
  simp only [responseSum_add, responseSum_scale,
    cancel_c3 A rates P hi he B C b hl, cancel_c4 A rates P hi he B C b hl hr,
    smul_zero, add_zero, sub_zero]

section Acceleration
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The second-order structure: only position enters the quadratic force,
and the force only enters acceleration. Q may be any bilinear gravity map. -/
def accelerationB (Q : V →ₗ[ℂ] V →ₗ[ℂ] V) :
    (V × V) →ₗ[ℂ] (V × V) →ₗ[ℂ] (V × V) where
  toFun x := {
    toFun := fun y => (0, Q x.1 y.1)
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  map_add' := by intros; ext y <;> simp
  map_smul' := by intros; ext y <;> simp

@[simp] theorem acceleration_left (Q : V →ₗ[ℂ] V →ₗ[ℂ] V) (f : V) (x : V × V) :
    accelerationB Q (0,f) x = 0 := by simp [accelerationB]

@[simp] theorem acceleration_right (Q : V →ₗ[ℂ] V →ₗ[ℂ] V) (f : V) (x : V × V) :
    accelerationB Q x (0,f) = 0 := by simp [accelerationB]

@[simp] theorem acceleration_position (Q : V →ₗ[ℂ] V →ₗ[ℂ] V) (x y : V × V) :
    LinearMap.fst ℂ V V (accelerationB Q x y) = 0 := rfl

end Acceleration
end GNC.QuadraticModalCancellation
