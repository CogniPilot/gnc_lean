import GNC.Analysis.ExponentialConvolution

/-! Analytic quadratic response of a constant linear operator with a finite
spectral resolution. The resolution is an explicit hypothesis, not a claim
that every matrix is diagonalizable. Polynomial factors in the forcing and
exact frequency resonance are supported. -/
noncomputable section
set_option autoImplicit false
namespace GNC.ModalQuadraticResponse
open ExponentialConvolution
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [Fintype I] [Fintype J]

def signal (ν : J → ℂ) (degree : J → ℕ) (c : J → E) (t : ℂ) : E :=
  ∑ j, mode (ν j) (degree j) t • c j

/-- Sum/difference frequencies arise algebraically from a bilinear forcing. -/
theorem quadratic_signal (ν : J → ℂ) (degree : J → ℕ) (c : J → E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (t : ℂ) :
    B (signal ν degree c t) (signal ν degree c t) =
      ∑ j, ∑ k, mode (ν j+ν k) (degree j+degree k) t • B (c j) (c k) := by
  simp only [signal, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul, mode_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [add_comm (ν k) (ν j), add_comm (degree k) (degree j)]

def forced (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (ν : ℂ) (n : ℕ) (b : E) (t : ℂ) : E :=
  ∑ i, moment (rates i) ν n t • P i b

@[simp] theorem forced_zero (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (ν : ℂ) (n : ℕ) (b : E) : forced rates P ν n b 0 = 0 := by
  simp [forced]

theorem derivative_forced (A : E →ₗ[ℂ] E) (rates : I → ℂ)
    (P : I → E →ₗ[ℂ] E)
    (hidentity : ∀ b, ∑ i, P i b = b)
    (heigen : ∀ i b, A (P i b) = rates i • P i b)
    (ν t : ℂ) (n : ℕ) (b : E) :
    HasDerivAt (forced rates P ν n b)
      (A (forced rates P ν n b t) + mode ν n t • b) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (derivative_moment (rates i) ν t n).smul_const (P i b))
  convert hd using 1
  simp only [forced, map_sum, map_smul, heigen, add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, hidentity]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_comm]

def response (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (ν : J → ℂ) (degree : J → ℕ) (c : J → E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (t : ℂ) : E :=
  ∑ j, ∑ k, forced rates P (ν j+ν k) (degree j+degree k) (B (c j) (c k)) t

@[simp] theorem response_zero (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (ν : J → ℂ) (degree : J → ℕ) (c : J → E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) : response rates P ν degree c B 0 = 0 := by
  simp [response]

/-- Zero-initial-data second response, with its differential equation proved
from the elementary expression. This does not solve the equation obtained
by evaluating the quadratic term along the corrected trajectory itself. -/
theorem derivative_response (A : E →ₗ[ℂ] E) (rates : I → ℂ)
    (P : I → E →ₗ[ℂ] E)
    (hidentity : ∀ b, ∑ i, P i b = b)
    (heigen : ∀ i b, A (P i b) = rates i • P i b)
    (ν : J → ℂ) (degree : J → ℕ) (c : J → E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (t : ℂ) :
    HasDerivAt (response rates P ν degree c B)
      (A (response rates P ν degree c B t) +
        B (signal ν degree c t) (signal ν degree c t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      derivative_forced A rates P hidentity heigen (ν j+ν k) t
        (degree j+degree k) (B (c j) (c k))))
  convert hd using 1
  simp [response, map_sum, Finset.sum_add_distrib, quadratic_signal]

theorem derivative_response_real [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hidentity : ∀ b, ∑ i, P i b = b)
    (heigen : ∀ i b, A (P i b) = rates i • P i b)
    (ν : J → ℂ) (degree : J → ℕ) (c : J → E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => response rates P ν degree c B (s : ℂ))
      (A (response rates P ν degree c B (t : ℂ)) +
        B (signal ν degree c (t : ℂ)) (signal ν degree c (t : ℂ))) t := by
  simpa using (derivative_response A rates P hidentity heigen ν degree c B (t : ℂ)).scomp
    t Complex.ofRealCLM.hasDerivAt

end GNC.ModalQuadraticResponse
