import GNC.Lie.AffineExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Corrected planar similarity exponential, including its removable zero
case. Both the rotational factor and translation kernel are identified with
mathlib's actual exponential/integral by differentiation and uniqueness. -/
noncomputable section
open Matrix NormedSpace Real
open scoped Matrix.Norms.Operator
namespace GNC.SimilarityExponential
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
def J : Mat2 := !![0,-1;1,0]
def generator (s θ : ℝ) : Mat2 := s • 1+θ • J
def scaledRotation (s θ t : ℝ) : Mat2 :=
  (Real.exp (s*t)*cos (θ*t)) • 1+(Real.exp (s*t)*sin (θ*t)) • J

theorem scaledRotation_derivative (s θ t : ℝ) :
    HasDerivAt (scaledRotation s θ) (generator s θ*scaledRotation s θ t) t := by
  have hE := ((hasDerivAt_id t).const_mul s).exp
  have hC := ((hasDerivAt_id t).const_mul θ).cos
  have hS := ((hasDerivAt_id t).const_mul θ).sin
  convert ((hE.mul hC).smul_const (1 : Mat2)).add ((hE.mul hS).smul_const J) using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [generator, scaledRotation, J, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> ring

theorem exp_generator (s θ t : ℝ) :
    exp (t • generator s θ) = scaledRotation s θ t := by
  have he := MixedInvariant.flow_unique (generator s θ) 0 1 (scaledRotation s θ)
    (fun r => by simpa using scaledRotation_derivative s θ r)
    (by simp [scaledRotation])
  simpa [MixedInvariant.flow] using (congrFun he t).symm

def alpha (s θ t : ℝ) : ℝ :=
  (s*(Real.exp (s*t)*cos (θ*t)-1)+θ*Real.exp (s*t)*sin (θ*t))/(s^2+θ^2)
def beta (s θ t : ℝ) : ℝ :=
  (θ*(1-Real.exp (s*t)*cos (θ*t))+s*Real.exp (s*t)*sin (θ*t))/(s^2+θ^2)

theorem alpha_derivative (s θ t : ℝ) (hd : s^2+θ^2 ≠ 0) :
    HasDerivAt (alpha s θ) (Real.exp (s*t)*cos (θ*t)) t := by
  have hE := ((hasDerivAt_id t).const_mul s).exp
  have hC := ((hasDerivAt_id t).const_mul θ).cos
  have hS := ((hasDerivAt_id t).const_mul θ).sin
  convert ((((hE.mul hC).sub_const 1).const_mul s).add
    ((hE.mul hS).const_mul θ)).div_const (s^2+θ^2) using 1
  · funext r; dsimp [alpha]; ring
  · simp only [id_eq, mul_one]
    field_simp
    ring

theorem beta_derivative (s θ t : ℝ) (hd : s^2+θ^2 ≠ 0) :
    HasDerivAt (beta s θ) (Real.exp (s*t)*sin (θ*t)) t := by
  have hE := ((hasDerivAt_id t).const_mul s).exp
  have hC := ((hasDerivAt_id t).const_mul θ).cos
  have hS := ((hasDerivAt_id t).const_mul θ).sin
  convert ((((hE.mul hC).const_sub 1).const_mul θ).add
    ((hE.mul hS).const_mul s)).div_const (s^2+θ^2) using 1
  · funext r; dsimp [beta]; ring
  · simp only [id_eq, mul_one]
    field_simp
    ring

theorem primitive_eq_coefficients (s θ t : ℝ) (hd : s^2+θ^2 ≠ 0) :
    AffineExponential.primitive (generator s θ) t = alpha s θ t • 1+beta s θ t • J := by
  let K : ℝ → Mat2 := fun r => alpha s θ r • 1+beta s θ r • J
  have hK (r : ℝ) : HasDerivAt K (exp (r • generator s θ)) r := by
    rw [exp_generator]
    exact ((alpha_derivative s θ r hd).smul_const (1 : Mat2)).add
      ((beta_derivative s θ r hd).smul_const J)
  have hD (r : ℝ) : HasDerivAt
      (fun z => AffineExponential.primitive (generator s θ) z-K z) 0 r := by
    simpa using (AffineExponential.primitive_derivative (generator s θ) r).sub (hK r)
  have hc := is_const_of_deriv_eq_zero (fun r => (hD r).differentiableAt)
    (fun r => (hD r).deriv) t 0
  have he : AffineExponential.primitive (generator s θ) t-K t = 0 := by
    simpa [K, alpha, beta, AffineExponential.primitive] using hc
  exact sub_eq_zero.mp he

def kernel (s θ : ℝ) : Mat2 :=
  if s = 0 ∧ θ = 0 then 1 else alpha s θ 1 • 1+beta s θ 1 • J

theorem kernel_eq_primitive (s θ : ℝ) :
    kernel s θ = AffineExponential.primitive (generator s θ) 1 := by
  by_cases h : s = 0 ∧ θ = 0
  · rcases h with ⟨rfl,rfl⟩
    simp [kernel, generator, AffineExponential.primitive_zero_generator]
  · have hd : s^2+θ^2 ≠ 0 := by
      intro he
      have hs : s = 0 := by nlinarith [sq_nonneg θ, sq_nonneg s]
      have ht : θ = 0 := by nlinarith [sq_nonneg θ, sq_nonneg s]
      exact h ⟨hs,ht⟩
    rw [kernel, if_neg h]
    exact (primitive_eq_coefficients s θ 1 hd).symm

/-- Corrected Theorem 8, strengthened from two to any finite number of
translation columns and with the missing zero case supplied. -/
theorem exp_similarity {n : Type*} [Fintype n] [DecidableEq n]
    (s θ : ℝ) (U : Matrix (Fin 2) n ℝ) :
    exp (Preintegration.block (generator s θ) U 0) =
      fromBlocks (scaledRotation s θ 1) (kernel s θ*U) 0 1 := by
  have he := AffineExponential.exp_block (generator s θ) U 1
  have hr : exp (generator s θ) = scaledRotation s θ 1 := by
    simpa using exp_generator s θ 1
  simpa [hr, ← kernel_eq_primitive] using he

end GNC.SimilarityExponential
