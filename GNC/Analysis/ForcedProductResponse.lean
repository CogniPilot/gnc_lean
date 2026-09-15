import GNC.Analysis.QuadraticModalCancellation

/-! The grouped forced-mode formula solves the complete first/second response
hierarchy. Error in each evaluated scalar kernel transfers to an explicit
finite weighted bound; no elementary-function or binary64 error is assumed
away. The higher-order physical gravity remainder is a separate obligation.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.ForcedProductResponse
open ForcedProductConvolution QuadraticModalCancellation
open scoped BigOperators

variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [Fintype I]

def signal (rates : I → ℂ) (P : I → E →ₗ[ℂ] E) (b : E) (t : ℂ) : E :=
  ∑ i, first (rates i) t • P i b

@[simp] theorem signal_initial (rates : I → ℂ) (P : I → E →ₗ[ℂ] E) (b : E) :
    signal rates P b 0 = 0 := by simp [signal]

theorem derivative_signal (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (b : E) (t : ℂ) :
    HasDerivAt (signal rates P b) (A (signal rates P b t)+b) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (derivative_first (rates i) t).smul_const (P i b))
  convert hd using 1
  simp only [signal, map_sum, map_smul, he, add_smul, one_smul,
    mul_smul, Finset.sum_add_distrib, hi]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_comm]

theorem source_reassembly (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E) (t : ℂ) :
    responseSum rates P B C b (fun _ y z => first y t*first z t) =
      C (B (signal rates P b t) (signal rates P b t)) := by
  conv_rhs => rw [← hi (B (signal rates P b t) (signal rates P b t))]
  simp only [signal, responseSum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

def response (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (b : E) (t : ℂ) : E :=
  responseSum rates P B LinearMap.id b (fun x y z => kernel x y z t)

@[simp] theorem response_initial (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (b : E) : response rates P B b 0 = 0 := by
  simp [response, responseSum]

theorem derivative_response (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (b : E) (t : ℂ) :
    HasDerivAt (response rates P B b)
      (A (response rates P B b t)+B (signal rates P b t) (signal rates P b t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        (derivative_kernel (rates i) (rates j) (rates k) t).smul_const
          (P i (B (P j b) (P k b))))))
  have hs := source_reassembly rates P hi B LinearMap.id b t
  simp only [LinearMap.id_apply] at hs
  rw [← hs]
  convert hd using 1
  simp only [response, responseSum, LinearMap.id_apply, map_sum, map_smul,
    he, add_smul, mul_smul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_comm]

/-- Restrict the complex modal expression to actual real time. -/
theorem derivative_response_real [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (A : E →ₗ[ℂ] E) (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (hi : ∀ b, ∑ i, P i b = b) (he : ∀ i b, A (P i b) = rates i • P i b)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (b : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => response rates P B b (s : ℂ))
      (A (response rates P B b (t : ℂ))+
        B (signal rates P b (t : ℂ)) (signal rates P b (t : ℂ))) t := by
  simpa using (derivative_response A rates P hi he B b (t : ℂ)).scomp
    t Complex.ofRealCLM.hasDerivAt

/-- A supplied scalar evaluation bound is multiplied by the actual projected
coefficient norm. The hypothesis must include truncation and rounding. -/
theorem evaluation_bound (rates : I → ℂ) (P : I → E →ₗ[ℂ] E)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E) (C : E →ₗ[ℂ] F) (b : E)
    (K reported : ℂ → ℂ → ℂ → ℂ) (eps : I → I → I → ℝ)
    (herr : ∀ i j k, ‖reported (rates i) (rates j) (rates k)-K (rates i) (rates j) (rates k)‖ ≤ eps i j k) :
    ‖responseSum rates P B C b reported-responseSum rates P B C b K‖ ≤
      ∑ i, ∑ j, ∑ k, eps i j k*‖C (P i (B (P j b) (P k b)))‖ := by
  rw [← responseSum_sub]
  unfold responseSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (herr i j k) (norm_nonneg _)

end GNC.ForcedProductResponse
