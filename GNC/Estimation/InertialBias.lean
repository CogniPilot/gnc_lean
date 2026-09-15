import GNC.Lie.RightJacobian
import GNC.Control.LogBackstepping
import Mathlib.Analysis.Real.Pi.Bounds

/-! Biased inertial navigation: the exact navigation-block benefit and its scope.

The extended input/bias vectors include the virtual position-rate component.
All comparisons use the same input and gravity. The bias coordinate is coupled
to the pose error; it is not a physical bias in new units. No Riccati-filter
dominance or linearity of the full augmented system is asserted.
-/
noncomputable section
open Matrix Real NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Estimation.InertialBias

def navigationDrift (g : Vec3) (x : LogState) : LogState :=
  ![x 1, g ⨯₃ x 2, 0]

def gravityGenerator (g : Vec3) : Mat5 := hat (velocityOnly g)-kinematicC

theorem hat_navigationDrift (g : Vec3) (x : LogState) :
    hat (navigationDrift g x) = gravityGenerator g*hat x-hat x*gravityGenerator g := by
  have he : navigationDrift g x = ![x 1,0,0]+ad (velocityOnly g) x := by
    ext i j; fin_cases i <;> simp [navigationDrift, ad, velocityOnly]
  rw [he]
  change hatLinear _ = _
  rw [map_add]
  change hat (![x 1,0,0] : LogState)+hat (ad (velocityOnly g) x) = _
  rw [hat_kinematic, hat_ad]
  simp only [Ring.lie_def, gravityGenerator]
  noncomm_ring

theorem navigationDrift_differential (g : Vec3) (x : LogState) :
    exp (hat x)*hat (Jacobian.blockRight x (navigationDrift g x)) =
      gravityGenerator g*exp (hat x)-exp (hat x)*gravityGenerator g := by
  rw [← left_right_differential, ← exp_fderiv_hat, hat_navigationDrift]
  have h := exp_commutator_fderiv (hat x) (-gravityGenerator g)
  simpa only [Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add, add_comm] using h

/-- Actual derivative of the right error of two biased INS matrix trajectories.
Biases need not be constant for this instantaneous navigation identity. -/
theorem right_error_derivative {X H : ℝ → SE23} {u b bh : LogState} {g : Vec3} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) (u-b) g) t)
    (hH : HasDerivAt (fun s => SE23.toMatrix (H s))
      (spacecraftDerivative (H t) (u-bh) g) t) :
    HasDerivAt (fun s => SE23.toMatrix (X s*(H s)⁻¹))
      (gravityGenerator g*SE23.toMatrix (X t*(H t)⁻¹)-
        SE23.toMatrix (X t*(H t)⁻¹)*gravityGenerator g-
        SE23.toMatrix (X t*(H t)⁻¹)*hat (adjoint (H t) (b-bh))) t := by
  have hd := hX.mul (matrix_inverse_derivative hH)
  simp only [SE23.toMatrix_mul]
  convert hd using 1
  rw [hat_adjoint]
  simp only [spacecraftDerivative, gravityGenerator]
  change _ = _
  have hb : hat (u-b) = hat u-hat b := hatLinear.map_sub u b
  have hh : hat (u-bh) = hat u-hat bh := hatLinear.map_sub u bh
  have hdif : hat (b-bh) = hat b-hat bh := hatLinear.map_sub b bh
  rw [hb, hh, hdif]
  have cancelH (Z : Mat5) : SE23.toMatrix (H t)⁻¹*(SE23.toMatrix (H t)*Z) = Z := by
    rw [← Matrix.mul_assoc, matrix_inv_mul, Matrix.one_mul]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, matrix_mul_inv, Matrix.mul_one, cancelH]
  noncomm_ring

/-- Coupled tangent-group bias coordinate, in (position,velocity,rotation) order. -/
def tangentBias (x eb : LogState) : LogState :=
  Jacobian.blockRightInverse x (-eb)

theorem tangentBias_reconstruct (x eb : LogState) (hθ : enorm (x 2) < 2*π) :
    Jacobian.blockRight x (tangentBias x eb) = -eb :=
  Jacobian.blockRight_inverse x (-eb) hθ

/-- Exact navigation log equation in tangent-group coordinates. The logarithm
is a differentiable lift of the actual right error, in the nonsingular chart.
This checks the key cancellation in Appendix B.4 of arXiv:2309.03765v3. -/
theorem navigation_log_equation {X H : ℝ → SE23} {x : ℝ → LogState}
    {dx u b bh : LogState} {g : Vec3} {t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) (u-b) g) t)
    (hH : HasDerivAt (fun s => SE23.toMatrix (H s))
      (spacecraftDerivative (H t) (u-bh) g) t)
    (hx : HasDerivAt x dx t)
    (he : ∀ s, X s*(H s)⁻¹ = groupExp (x s))
    (hθ : enorm (x t 2) < 2*π) :
    dx = navigationDrift g (x t)+tangentBias (x t) (adjoint (H t) (b-bh)) := by
  have hd := right_error_derivative hX hH
  simp_rw [he, groupExp_toMatrix] at hd
  have hu := (matrixExp_right_derivative hx).unique hd
  have hj : Jacobian.blockRight (x t)
      (navigationDrift g (x t)+tangentBias (x t) (adjoint (H t) (b-bh))) =
      Jacobian.blockRight (x t) (navigationDrift g (x t))-
        adjoint (H t) (b-bh) := by
    rw [Jacobian.blockRight, blockLeft_add]
    change _ = _
    rw [← Jacobian.blockRight, ← Jacobian.blockRight, tangentBias_reconstruct _ _ hθ]
    rfl
  have hm : exp (hat (x t))*hat (Jacobian.blockRight (x t) dx) =
      exp (hat (x t))*hat (Jacobian.blockRight (x t)
        (navigationDrift g (x t)+tangentBias (x t) (adjoint (H t) (b-bh)))) := by
    rw [hj]
    change _ = exp (hat (x t))*hatLinear _
    rw [map_sub, Matrix.mul_sub]
    change _ = exp (hat (x t))*hat (Jacobian.blockRight (x t)
      (navigationDrift g (x t)))-exp (hat (x t))*hat (adjoint (H t) (b-bh))
    rw [navigationDrift_differential]
    exact hu
  have hc := congrArg (fun Z => exp (-hat (x t))*Z) hm
  simp only [← Matrix.mul_assoc, MixedInvariant.exp_cancel', Matrix.one_mul] at hc
  have hi := congrArg (Jacobian.blockRightInverse (x t)) (hat_injective hc)
  simpa only [Jacobian.blockRightInverse_right _ _ hθ] using hi

/-- Standard log-attitude propagation for a transported gyro-bias error c. -/
def gyroLogRate (q c : Vec3) : Vec3 := -Jacobian.inverseAt (-q) c

@[simp] theorem gyroLogRate_zero (c : Vec3) : gyroLogRate 0 c = -c := by
  simp [gyroLogRate, Jacobian.inverseAt]

/-- The exact discrepancy from the ordinary first-order bias term -c. -/
def gyroRemainder (q c : Vec3) : Vec3 := gyroLogRate q c+c

theorem tangentBias_rotation (x eb : LogState) :
    tangentBias x eb 2 = gyroLogRate (x 2) (eb 2) := by
  ext i; fin_cases i <;>
    simp [tangentBias, Jacobian.blockRightInverse, Jacobian.blockInverse,
      gyroLogRate, Jacobian.inverseAt, crossProduct, vecHead, vecTail] <;> ring

/-- The changed bias coordinate has its own nonlinear dynamics, even when
the transported physical gyro bias c is constant. -/
theorem gyroLogRate_path_derivative {q : ℝ → Vec3} {dq c : Vec3} {t : ℝ}
    (hq : HasDerivAt q dq t) (hpos : 0 < enorm (q t)) (hπ : enorm (q t) < π) :
    HasDerivAt (fun s => gyroLogRate (q s) c)
      (-Jacobian.inverseDerivative (-q t) (-dq) c) t := by
  have h := (Jacobian.inverseAt_path_derivative hq.neg (hasDerivAt_const t c)
    (by simpa only [Pi.neg_apply, enorm_neg] using hpos)
    (by simpa only [Pi.neg_apply, enorm_neg] using hπ)).neg
  simpa only [Pi.neg_apply, Jacobian.inverseAt, map_zero, LinearMap.zero_apply,
    smul_zero, sub_zero, add_zero, gyroLogRate] using h

/-- Removing this vector remainder does not improve the radial attitude-energy
supply: the remainder is exactly orthogonal to the attitude error. -/
theorem gyroRemainder_radial (q c : Vec3) : q ⬝ᵥ gyroRemainder q c = 0 := by
  simp [gyroRemainder, gyroLogRate, dotProduct_add,
    LogBackstepping.inverse_right_radial_pairing]

theorem gyro_energy_derivative {q : ℝ → Vec3} {c : Vec3} {t : ℝ}
    (hq : HasDerivAt q (gyroLogRate (q t) c) t) :
    HasDerivAt (fun s => lengthSq (q s)) (-2*(q t ⬝ᵥ c)) t := by
  simpa [gyroLogRate, LogBackstepping.inverse_right_radial_pairing] using
    LogBackstepping.lengthSq_derivative hq

theorem axis_enorm (θ : ℝ) (hθ : 0 ≤ θ) : enorm (![0,0,θ] : Vec3) = θ := by
  have hs := enorm_sq (![0,0,θ] : Vec3)
  simp [lengthSq] at hs
  nlinarith [enorm_nonneg (![0,0,θ] : Vec3)]

/-- Explicit nonzero finite-error coupling for a perpendicular gyro bias. -/
theorem perpendicular_gyro_remainder (θ β : ℝ) (hθ : 0 < θ) :
    gyroRemainder ![0,0,θ] ![β,0,0] =
      ![β*Coefficients.beta θ, -θ*β/2, 0] := by
  have hn : enorm (![0,0,-θ] : Vec3) = θ := by
    rw [show (![0,0,-θ] : Vec3) = -(![0,0,θ] : Vec3) by ext i; fin_cases i <;> simp,
      enorm_neg, axis_enorm θ hθ.le]
  ext i; fin_cases i <;>
    simp [gyroRemainder, gyroLogRate, Jacobian.inverseAt, hn,
      crossProduct, vecHead, vecTail] <;>
    field_simp <;> ring

theorem perpendicular_gyro_remainder_sq (θ β : ℝ) (hθ : 0 < θ) :
    enorm (gyroRemainder ![0,0,θ] ![β,0,0])^2 =
      β^2*(Coefficients.beta θ^2+θ^2/4) := by
  rw [perpendicular_gyro_remainder θ β hθ, enorm_sq]
  simp [lengthSq]
  ring

theorem perpendicular_gyro_remainder_lower (θ β : ℝ) (hθ : 0 < θ) :
    θ*|β|/2 ≤ enorm (gyroRemainder ![0,0,θ] ![β,0,0]) := by
  have he := perpendicular_gyro_remainder_sq θ β hθ
  have hp := mul_nonneg (sq_nonneg β) (sq_nonneg (Coefficients.beta θ))
  nlinarith [enorm_nonneg (gyroRemainder ![0,0,θ] ![β,0,0]),
    abs_nonneg β, sq_abs β]

/-- With aligned rotation and bias there is no such navigation-block gain. -/
theorem parallel_gyro_remainder (q : Vec3) (β : ℝ) : gyroRemainder q (β • q) = 0 := by
  simp [gyroRemainder, gyroLogRate, Jacobian.inverseAt, map_smul]

/-- A concrete nonlinear bias-coordinate derivative along an actual attitude
log ODE. The physical transported gyro bias is the constant vector (β,0,0).
The first-order transformed bias equation at zero reference angular rate
would predict zero; the exact derivative below is generally nonzero. -/
theorem perpendicular_bias_coordinate_derivative {q : ℝ → Vec3} {t θ β : ℝ}
    (hθ : 0 < θ) (hπ : θ < π) (hqt : q t = ![0,0,θ])
    (hq : HasDerivAt q (gyroLogRate (q t) ![β,0,0]) t) :
    HasDerivAt (fun s => gyroLogRate (q s) ![β,0,0])
      ![0,0,β^2*(Coefficients.beta θ*(1-Coefficients.beta θ)/θ-θ/4)] t := by
  have hn : enorm (q t) = θ := by rw [hqt, axis_enorm θ hθ.le]
  have h := gyroLogRate_path_derivative (c := ![β,0,0]) hq (by simpa [hn]) (by simpa [hn])
  convert h using 1
  rw [hqt]
  have hn' : enorm (-(![0,0,θ] : Vec3)) = θ := by rw [enorm_neg, axis_enorm θ hθ.le]
  simp only [gyroLogRate, Jacobian.inverseDerivative, Jacobian.inverseAt, hn']
  ext i; fin_cases i <;>
    simp [crossProduct, vecHead, vecTail, dotProduct, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem beta_half_pi : Coefficients.beta (π/2) = 1-π/4 := by
  rw [Coefficients.beta, show π/2/2 = π/4 by ring, cos_pi_div_four, sin_pi_div_four,
    div_self (by positivity : Real.sqrt 2/2 ≠ 0)]
  ring

/-- At ninety degrees the transformed bias derivative is explicitly nonzero
for every nonzero perpendicular physical gyro bias. -/
theorem quarter_turn_bias_coordinate_derivative {q : ℝ → Vec3} {t β : ℝ}
    (hqt : q t = ![0,0,π/2])
    (hq : HasDerivAt q (gyroLogRate (q t) ![β,0,0]) t) :
    HasDerivAt (fun s => gyroLogRate (q s) ![β,0,0])
      ![0,0,β^2*(1/2-π/4)] t := by
  have h := perpendicular_bias_coordinate_derivative (by positivity : 0 < π/2)
    (by linarith [pi_pos] : π/2 < π) hqt hq
  convert h using 1
  rw [beta_half_pi]
  apply congrArg (fun z : ℝ => (![0,0,z] : Vec3))
  field_simp [Real.pi_ne_zero]
  ring

theorem quarter_turn_bias_coordinate_nonzero (β : ℝ) (hβ : β ≠ 0) :
    (![0,0,β^2*(1/2-π/4)] : Vec3) ≠ 0 := by
  have hn : β^2*(1/2-π/4) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hβ) (by linarith [Real.pi_gt_three])
  intro he
  have hz := congrFun he 2
  change β^2*(1/2-π/4) = 0 at hz
  linarith

end GNC.Estimation.InertialBias
