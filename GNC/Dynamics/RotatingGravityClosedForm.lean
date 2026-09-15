import GNC.Dynamics.RotatingGravityPolynomial
import GNC.Analysis.BiquadraticExponential
import GNC.Dynamics.RadialGravityFrame

/-! Elementary transition and constant-input response for a circular reference
with a constant radial thrust. The gravity-gradient approximation is retained;
this does not assert a closed form for the full nonlinear inverse-square orbit. -/
noncomputable section
namespace GNC.RotatingGravity
open Matrix Real QuadraticModes
open scoped Matrix Matrix.Norms.Operator

def discriminant (k w : ℝ) : ℝ := k*(9*k-8*w^2)
def plusRoot (k w : ℝ) : ℝ := (k-2*w^2+sqrt (discriminant k w))/2
def minusRoot (k w : ℝ) : ℝ := (k-2*w^2-sqrt (discriminant k w))/2

theorem discriminant_positive {k w : ℝ} (hk : 0 < k) (hw : w^2 ≤ k) :
    0 < discriminant k w := by
  unfold discriminant
  apply mul_pos hk
  linarith

theorem roots_distinct {k w : ℝ} (hk : 0 < k) (hw : w^2 ≤ k) :
    plusRoot k w ≠ minusRoot k w := by
  have hs := sqrt_pos.2 (discriminant_positive hk hw)
  unfold plusRoot minusRoot
  linarith

theorem roots_sum (k w : ℝ) : plusRoot k w + minusRoot k w = k-2*w^2 := by
  unfold plusRoot minusRoot; ring

theorem roots_product {k w : ℝ} (hd : 0 ≤ discriminant k w) :
    plusRoot k w * minusRoot k w = (w^2-k)*(w^2+2*k) := by
  have hs := sq_sqrt hd
  unfold plusRoot minusRoot
  unfold discriminant at hs ⊢
  nlinarith

theorem powered_root_signs {k w : ℝ} (hk : 0 < k) (hw : w^2 < k) :
    0 < plusRoot k w ∧ minusRoot k w < 0 := by
  have hd := discriminant_positive hk hw.le
  have hs := sqrt_pos.2 hd
  have hlt : minusRoot k w < plusRoot k w := by unfold minusRoot plusRoot; linarith
  have hprod := roots_product hd.le
  have hneg : (w^2-k)*(w^2+2*k) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hw) (by positivity)
  constructor
  · by_contra h
    have hp := le_of_not_gt h
    have hm : minusRoot k w ≤ 0 := le_trans hlt.le hp
    have := mul_nonneg_of_nonpos_of_nonpos hp hm
    linarith
  · by_contra h
    have hm := le_of_not_gt h
    have hp : 0 ≤ plusRoot k w := le_trans hm hlt.le
    have := mul_nonneg hp hm
    linarith

theorem planar_biquadratic {k w : ℝ} (hd : 0 ≤ discriminant k w) :
    planar k w ^ 4 = (plusRoot k w + minusRoot k w) • planar k w ^ 2 -
      (plusRoot k w * minusRoot k w) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [roots_sum, roots_product hd]
  have he := planar_relation k w
  have hc : k-2*w^2 = -(2*w^2-k) := by ring
  rw [hc, neg_smul]
  exact eq_sub_of_add_eq (eq_neg_of_add_eq_zero_left (by simpa [add_right_comm] using he))

/-- The actual four-dimensional rotating gravity matrix has an elementary
Rodrigues-style exponential. The hypotheses cover the powered-circle example
and include the zero-thrust HCW limit. -/
theorem planar_exp {k w : ℝ} (hk : 0 < k) (hw : w^2 ≤ k) (t : ℝ) :
    NormedSpace.exp (t • planar k w) =
      transition (planar k w) (plusRoot k w) (minusRoot k w) t :=
  exp_biquadratic _ _ _ _ (roots_distinct hk hw)
    (planar_biquadratic (discriminant_positive hk hw).le)

/-- The independent out-of-plane position/velocity block is exact too. -/
theorem normal_exp (k t : ℝ) :
    NormedSpace.exp (t • normal k) =
      C (-k) t • (1 : Matrix (Fin 2) (Fin 2) ℝ) + S (-k) t • normal k :=
  exp_quadratic _ _ _ (normal_relation k)

/-- Reorder (position, rotating-coordinate velocity) into planar and normal
states. The closed-form matrix is the existing physical frame model. -/
def originalIndex : (Fin 4 ⊕ Fin 2) ≃ (Fin 3 ⊕ Fin 3) where
  toFun := Sum.elim (fun i => ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1] i)
    (fun i => ![Sum.inl 2, Sum.inr 2] i)
  invFun := Sum.elim (fun i => ![Sum.inl 0, Sum.inl 1, Sum.inr 0] i)
    (fun i => ![Sum.inl 2, Sum.inl 3, Sum.inr 1] i)
  left_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl

theorem physical_block_decomposition (k w : ℝ) :
    (RotatingVariational.classicalGenerator (RadialGravityFrame.gravity k)
      (RadialGravityFrame.omega w) (RadialGravityFrame.omega 0)).submatrix
        originalIndex originalIndex = fromBlocks (planar k w) 0 0 (normal k) := by
  rw [RadialGravityFrame.classical_blocks]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [submatrix_apply, originalIndex, planar, normal, fromBlocks, sub_eq_add_neg, add_comm]

theorem hcw_roots {k w : ℝ} (hk : 0 ≤ k) (hw : w^2 = k) :
    plusRoot k w = 0 ∧ minusRoot k w = -k := by
  have hd : discriminant k w = k^2 := by unfold discriminant; rw [hw]; ring
  simp only [plusRoot, minusRoot, hw, hd, sqrt_sq hk]
  constructor <;> ring

/-- Constant forcing is included by the elementary antiderivative, without
requiring that the dynamics matrix be invertible. -/
theorem planar_forced_solution {k w : ℝ} (hk : 0 < k) (hw : w^2 ≤ k)
    (X₀ B : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) :
    HasDerivAt (fun s => transition (planar k w) (plusRoot k w) (minusRoot k w) s * X₀ +
      forced (planar k w) (plusRoot k w) (minusRoot k w) s * B)
      (planar k w * (transition (planar k w) (plusRoot k w) (minusRoot k w) t * X₀ +
        forced (planar k w) (plusRoot k w) (minusRoot k w) t * B) + B) t :=
  forced_solution _ _ _ _ _ _ (roots_distinct hk hw)
    (planar_biquadratic (discriminant_positive hk hw).le)

end GNC.RotatingGravity
