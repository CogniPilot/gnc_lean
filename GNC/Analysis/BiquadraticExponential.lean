import GNC.Analysis.QuadraticModes

/-! Rodrigues-style elementary exponential for a biquadratic annihilator.
The two roots are roots in the *square* of the generator and must be distinct.
Either root may vanish or be negative. -/
noncomputable section
namespace GNC.QuadraticModes
section Projectors
variable {A 𝕜 : Type*} [Ring A] [Field 𝕜] [Algebra 𝕜 A]

def projector (W : A) (p q : 𝕜) : A := (p-q)⁻¹ • (W^2-q • 1)

theorem projector_sum (W : A) (p q : 𝕜) (hpq : p ≠ q) :
    projector W p q + projector W q p = 1 := by
  have hd : p-q ≠ 0 := sub_ne_zero.mpr hpq
  have hi : (q-p)⁻¹ = -(p-q)⁻¹ := by rw [← neg_sub p q, inv_neg]
  unfold projector
  rw [hi]
  calc
    _ = ((p-q)⁻¹*(p-q)) • (1 : A) := by module
    _ = 1 := by rw [inv_mul_cancel₀ hd, one_smul]

theorem projector_square (W : A) (p q : 𝕜)
    (hW : W^4 = (p+q) • W^2 - (p*q) • (1 : A)) :
    W^2 * projector W p q = p • projector W p q := by
  unfold projector
  simp only [mul_smul_comm, mul_sub, mul_one]
  rw [show W^2*W^2 = W^4 by noncomm_ring, hW]
  module

end Projectors
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def transition (W : A) (p q t : ℝ) : A :=
  (C p t • (1 : A) + S p t • W) * projector W p q +
  (C q t • (1 : A) + S q t • W) * projector W q p

theorem derivative_mode (W E : A) (p t : ℝ) (hE : W^2*E = p • E) :
    HasDerivAt (fun s => (C p s • (1 : A) + S p s • W)*E)
      (W*((C p t • (1 : A) + S p t • W)*E)) t := by
  convert (((derivative_C p t).smul_const (1 : A)).add
    ((derivative_S p t).smul_const W)).mul_const E using 1
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, one_mul,
    ← mul_assoc, ← pow_two, hE, smul_smul]
  module

theorem exp_quadratic [CompleteSpace A] (W : A) (p t : ℝ)
    (hW : W^2 = p • (1 : A)) :
    NormedSpace.exp (t • W) = C p t • (1 : A) + S p t • W := by
  have hd (s : ℝ) := derivative_mode W 1 p s (by simpa using hW)
  have he := MixedInvariant.flow_unique W 0 1
    (fun s => C p s • (1 : A) + S p s • W)
    (fun s => by simpa using hd s) (by simp)
  simpa [MixedInvariant.flow] using (congrFun he t).symm

/-- The four matrix coefficients, making the finite polynomial explicit. -/
theorem transition_polynomial (W : A) (p q t : ℝ) :
    transition W p q t =
      ((p*C q t-q*C p t)/(p-q)) • (1 : A) +
      ((p*S q t-q*S p t)/(p-q)) • W +
      ((C p t-C q t)/(p-q)) • W^2 +
      ((S p t-S q t)/(p-q)) • W^3 := by
  unfold transition projector
  rw [show (q-p)⁻¹ = -(p-q)⁻¹ by rw [← neg_sub p q, inv_neg]]
  simp only [mul_smul_comm, add_mul, mul_sub, smul_mul_assoc, mul_one, one_mul,
    show W*W^2 = W^3 by noncomm_ring, div_eq_mul_inv]
  module

theorem derivative_transition (W : A) (p q t : ℝ)
    (hW : W^4 = (p+q) • W^2 - (p*q) • (1 : A)) :
    HasDerivAt (transition W p q) (W * transition W p q t) t := by
  have hW' : W^4 = (q+p) • W^2 - (q*p) • (1 : A) := by simpa [add_comm, mul_comm] using hW
  simpa only [transition, mul_add] using
    (derivative_mode W (projector W p q) p t (projector_square W p q hW)).add
      (derivative_mode W (projector W q p) q t (projector_square W q p hW'))

/-- Equality to mathlib's exponential, with explicit elementary coefficients. -/
theorem exp_biquadratic [CompleteSpace A] (W : A) (p q t : ℝ) (hpq : p ≠ q)
    (hW : W^4 = (p+q) • W^2 - (p*q) • (1 : A)) :
    NormedSpace.exp (t • W) = transition W p q t := by
  have he := MixedInvariant.flow_unique W 0 1 (transition W p q)
    (fun s => by simpa using derivative_transition W p q s hW)
    (by simpa [transition] using projector_sum W p q hpq)
  simpa [MixedInvariant.flow] using (congrFun he t).symm

/-- Elementary integral of the transition. This avoids an inverse of W,
including in the singular unforced circular-orbit limit. -/
def forced (W : A) (p q t : ℝ) : A :=
  (S p t • (1 : A) + J p t • W) * projector W p q +
  (S q t • (1 : A) + J q t • W) * projector W q p

theorem derivative_forced (W : A) (p q t : ℝ) :
    HasDerivAt (forced W p q) (transition W p q t) t := by
  exact ((((derivative_S p t).smul_const (1 : A)).add
    ((derivative_J p t).smul_const W)).mul_const (projector W p q)).add
    ((((derivative_S q t).smul_const (1 : A)).add
      ((derivative_J q t).smul_const W)).mul_const (projector W q p))

theorem forced_mode (W E : A) (p t : ℝ) (hE : W^2*E = p • E) :
    (C p t • (1 : A) + S p t • W)*E =
      W*((S p t • (1 : A) + J p t • W)*E) + E := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, one_mul,
    ← mul_assoc, ← pow_two, hE, smul_smul, C_eq_one_add p t]
  module

theorem forced_relation (W : A) (p q t : ℝ) (hpq : p ≠ q)
    (hW : W^4 = (p+q) • W^2 - (p*q) • (1 : A)) :
    transition W p q t = W * forced W p q t + 1 := by
  have hW' : W^4 = (q+p) • W^2 - (q*p) • (1 : A) := by simpa [add_comm, mul_comm] using hW
  unfold transition forced
  rw [forced_mode W (projector W p q) p t (projector_square W p q hW),
    forced_mode W (projector W q p) q t (projector_square W q p hW')]
  rw [mul_add, ← projector_sum W p q hpq]
  abel

@[simp] theorem forced_zero (W : A) (p q : ℝ) : forced W p q 0 = 0 := by simp [forced]

/-- Initial state and a constant forcing, in any real Banach algebra. -/
theorem forced_solution (W X₀ B : A) (p q t : ℝ) (hpq : p ≠ q)
    (hW : W^4 = (p+q) • W^2 - (p*q) • (1 : A)) :
    HasDerivAt (fun s => transition W p q s * X₀ + forced W p q s * B)
      (W*(transition W p q t * X₀ + forced W p q t * B) + B) t := by
  convert ((derivative_transition W p q t hW).mul_const X₀).add
    ((derivative_forced W p q t).mul_const B) using 1
  rw [forced_relation W p q t hpq hW]
  noncomm_ring

end GNC.QuadraticModes
