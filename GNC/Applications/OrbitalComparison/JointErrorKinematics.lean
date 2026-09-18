import GNC.Applications.OrbitalComparison.JointErrorReference

/-! Exact reconstruction of the three-axis Lie candidate. The attitude
offset is fixed in the inertial frame; the reference and force vary in time.
Derivatives retain the reference's complete gravitational acceleration. -/
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial PointingCapPolynomial LieSTTOutput SpatialBurn
noncomputable section

private theorem polynomial_value (p : PointingCapPolynomial.Vector) (x : Vec3) (t : ℝ) :
    PointingCapPolynomial.vectorValue p x t=WithLp.toLp 2 (value3 p x t) := by
  ext i
  fin_cases i <;> simp [PointingCapPolynomial.vectorValue,value3,pack_eq]

def position (x : Vec3) (t : ℝ) : E3 :=
  WithLp.toLp 2 (exactReference t)+
    LieRadiusFrame.left x (PointingCapPolynomial.vectorValue modelInput.rho x t)

def velocity (x : Vec3) (t : ℝ) : E3 :=
  referenceVelocity t+LieRadiusFrame.left x
    (PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative modelInput.rho) x t)

def acceleration (x : Vec3) (t : ℝ) : E3 :=
  Gravity.field (modelInput.K:ℝ) (WithLp.toLp 2 (exactReference t))+
    WithLp.toLp 2 (exactForce t)+LieRadiusFrame.left x
      (PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative
        (PointingCapPolynomial.derivative modelInput.rho)) x t)

def thrust (x : Vec3) (t : ℝ) : E3 := WithLp.toLp 2 (rotate (rotationExp x) (exactForce t))

theorem position_derivative (x : Vec3) (t : ℝ) :
    HasDerivAt (position x) (velocity x t) t :=
  (reference_position_derivative t).add
    (LieRadiusFrame.left_derivative x (PointingCapPolynomial.vector_derivative _ _ _))

theorem velocity_derivative (x : Vec3) (t : ℝ) :
    HasDerivAt (velocity x) (acceleration x t) t :=
  (reference_velocity_derivative t).add
    (LieRadiusFrame.left_derivative x (PointingCapPolynomial.vector_derivative _ _ _))

theorem position_value (x : Vec3) (t : ℝ) :
    (position x t).ofLp=exactReference t+Jacobian.leftAt x (value3 modelInput.rho x t) := by
  simp only [position,LieRadiusFrame.left,polynomial_value]
  rfl

theorem physical_defect_value (x : Vec3) (t : ℝ) :
    ‖acceleration x t-(Gravity.field (modelInput.K:ℝ) (position x t)+thrust x t)‖=
      enorm (Gravity.field3 (modelInput.K:ℝ) (exactReference t)+exactForce t+
        Jacobian.leftAt x (value3 (PointingCapPolynomial.derivative
          (PointingCapPolynomial.derivative modelInput.rho)) x t)-
        (Gravity.field3 (modelInput.K:ℝ) (exactReference t+Jacobian.leftAt x (value3 modelInput.rho x t))+
          rotate (rotationExp x) (exactForce t))) := by
  simp only [acceleration,position,thrust,LieRadiusFrame.left,polynomial_value]
  rfl

/-- The candidate radius floor follows from the Lie translation bound and
the exact unit-radius reference. No unknown physical trajectory is assumed. -/
theorem position_radius {x : Vec3} {t P : ℝ} (hx : enorm x<2*Real.pi)
    (hρ : enorm (value3 modelInput.rho x t)≤P) : 1-P≤‖position x t‖ := by
  have hρ' : ‖PointingCapPolynomial.vectorValue modelInput.rho x t‖≤P := by
    simpa only [←value3_norm] using hρ
  have hd := (LieRadiusFrame.left_norm x hx
    (PointingCapPolynomial.vectorValue modelInput.rho x t)).trans hρ'
  have hn := norm_sub_le (position x t)
    (LieRadiusFrame.left x (PointingCapPolynomial.vectorValue modelInput.rho x t))
  rw [position,add_sub_cancel_right] at hn
  change enorm (exactReference t)≤_ at hn
  rw [exactReference_norm] at hn
  change 1≤‖position x t‖+‖LieRadiusFrame.left x
    (PointingCapPolynomial.vectorValue modelInput.rho x t)‖ at hn
  linarith

end
end GNC.OrbitalComparison.JointErrorData
