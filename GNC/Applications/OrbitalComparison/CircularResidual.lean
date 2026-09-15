import GNC.Applications.OrbitalComparison.PoweredCircle
import GNC.Applications.OrbitalComparison.NumericalPrediction

/-! Physical meaning of the rotating-frame differential defect used by the
common finite-burn checker. The reference rotation is exact. Both Coriolis
terms, the centrifugal term, the actual gravity gradient and the actual
gravity Hessian are retained. The reported velocity is inertial velocity.
-/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace GNC.OrbitalComparison.PoweredCircle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def Plane.mix (B : Plane E) (a x y : ℝ) : E := x • B.radial a+y • B.tangent a

def Plane.rotated (B : Plane E) (a : ℝ) : Plane E where
  x := B.radial a
  y := B.tangent a
  norm_x := B.norm_radial a
  norm_y := B.norm_tangent a
  orthogonal := by
    simp only [Plane.radial,Plane.tangent,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
      B.norm_x,B.norm_y,B.orthogonal,B.orthogonal_rev]
    ring

theorem Plane.mix_norm_sq (B : Plane E) (a x y : ℝ) :
    ‖B.mix a x y‖^2 = x^2+y^2 := (B.rotated a).norm_combination x y

theorem Plane.mix_add (B : Plane E) (a x y u v : ℝ) :
    B.mix a (x+u) (y+v) = B.mix a x y+B.mix a u v := by
  dsimp [Plane.mix]
  module
theorem Plane.mix_scale (B : Plane E) (a c x y : ℝ) :
    B.mix a (c*x) (c*y) = c • B.mix a x y := by
  dsimp [Plane.mix]
  module

theorem Plane.mix_derivative (B : Plane E) {x y : ℝ → ℝ} {dx dy t : ℝ}
    (hx : HasDerivAt x dx t) (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => B.mix (rate*s) (x s) (y s))
      (B.mix (rate*t) (dx-rate*y t) (dy+rate*x t)) t := by
  have ht : HasDerivAt (fun s : ℝ => rate*s) rate t := by
    simpa using (hasDerivAt_id t).const_mul rate
  convert (hx.smul (B.radial_derivative ht)).add (hy.smul (B.tangent_derivative ht)) using 1
  dsimp [Plane.mix]
  module

/-- The quadratic gravity field in an arbitrary orthonormal plane, with
the same SI scaling as the numerical certificate. -/
theorem Plane.quadratic_components (B : Plane E) (x y : ℝ) :
    Gravity.gradient mu ((7000000:ℝ) • B.x) ((7000000:ℝ) • (x • B.x+y • B.y))+
      (1/2:ℝ) • Gravity.hessian mu ((7000000:ℝ) • B.x)
        ((7000000:ℝ) • (x • B.x+y • B.y)) ((7000000:ℝ) • (x • B.x+y • B.y)) =
      (mu/7000000^2) • ((2*x-3*x^2+3/2*y^2) • B.x+(-y+3*x*y) • B.y) := by
  simp only [Gravity.gradient,Gravity.hessian,norm_smul,Real.norm_eq_abs,B.norm_x,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,B.norm_y,B.orthogonal,B.orthogonal_rev,B.norm_combination]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 7000000),one_pow,mul_one,mul_zero,
    add_zero,zero_add]
  simp only [mul_pow,B.norm_combination]
  module

def gradientScale : ℝ := 360000*mu/7000000^3
def forceScale : ℝ := 360000*thrust/7000000

theorem Plane.quadratic_acceleration (B : Plane E) (t θ x y : ℝ) :
    quadraticAcceleration (B.reference t) ((7000000:ℝ) • B.mix (rate*t) x y) (B.force θ t) =
      (7000000:ℝ) • B.mix (rate*t)
        (gradientScale*(2*x-3*x^2+3/2*y^2)-forceScale*(1-Real.cos θ))
        (gradientScale*(-y+3*x*y)+forceScale*Real.sin θ) := by
  unfold quadraticAcceleration
  have h := (B.rotated (rate*t)).quadratic_components x y
  change Gravity.gradient mu (B.reference t) ((7000000:ℝ) • B.mix (rate*t) x y)+
    (1/2:ℝ) • Gravity.hessian mu (B.reference t) ((7000000:ℝ) • B.mix (rate*t) x y)
      ((7000000:ℝ) • B.mix (rate*t) x y) = _ at h
  rw [h,B.force_decomposition]
  dsimp [Plane.rotated,Plane.mix,Plane.sineForce,Plane.cosineForce,gradientScale,forceScale]
  module

structure PositionCurve where
  x : ℝ → ℝ
  y : ℝ → ℝ
  dx : ℝ → ℝ
  dy : ℝ → ℝ
  ddx : ℝ → ℝ
  ddy : ℝ → ℝ
  derivative_x : ∀ t, HasDerivAt x (dx t) t
  derivative_y : ∀ t, HasDerivAt y (dy t) t
  derivative_dx : ∀ t, HasDerivAt dx (ddx t) t
  derivative_dy : ∀ t, HasDerivAt dy (ddy t) t

def PositionCurve.position (P : PositionCurve) (B : Plane E) (t : ℝ) : E :=
  (7000000:ℝ) • B.mix (rate*t) (P.x t) (P.y t)
def PositionCurve.velocity (P : PositionCurve) (B : Plane E) (t : ℝ) : E :=
  (7000000:ℝ) • B.mix (rate*t) (P.dx t-rate*P.y t) (P.dy t+rate*P.x t)
def PositionCurve.acceleration (P : PositionCurve) (B : Plane E) (t : ℝ) : E :=
  (7000000:ℝ) • B.mix (rate*t)
    (P.ddx t-2*rate*P.dy t-rate^2*P.x t)
    (P.ddy t+2*rate*P.dx t-rate^2*P.y t)

theorem PositionCurve.position_derivative (P : PositionCurve) (B : Plane E) (t : ℝ) :
    HasDerivAt (P.position B) (P.velocity B t) t :=
  (B.mix_derivative (P.derivative_x t) (P.derivative_y t)).const_smul 7000000

theorem PositionCurve.velocity_derivative (P : PositionCurve) (B : Plane E) (t : ℝ) :
    HasDerivAt (P.velocity B) (P.acceleration B t) t := by
  have h := (B.mix_derivative
    ((P.derivative_dx t).sub ((P.derivative_y t).const_mul rate))
    ((P.derivative_dy t).add ((P.derivative_x t).const_mul rate))).const_smul (7000000:ℝ)
  convert h using 1
  dsimp [PositionCurve.acceleration]
  congr 2 <;> ring

def PositionCurve.residualX (P : PositionCurve) (θ t : ℝ) : ℝ :=
  P.ddx t-2*rate*P.dy t-(rate^2+2*gradientScale)*P.x t+
    3*gradientScale*(P.x t)^2-(3/2)*gradientScale*(P.y t)^2+
    forceScale*(1-Real.cos θ)
def PositionCurve.residualY (P : PositionCurve) (θ t : ℝ) : ℝ :=
  P.ddy t+2*rate*P.dx t+(gradientScale-rate^2)*P.y t-
    3*gradientScale*P.x t*P.y t-forceScale*Real.sin θ

theorem PositionCurve.physical_residual (P : PositionCurve) (B : Plane E) (θ t : ℝ) :
    P.acceleration B t-quadraticAcceleration (B.reference t) (P.position B t) (B.force θ t) =
      (7000000:ℝ) • B.mix (rate*t) (P.residualX θ t) (P.residualY θ t) := by
  rw [PositionCurve.position,B.quadratic_acceleration]
  dsimp [PositionCurve.acceleration,PositionCurve.residualX,PositionCurve.residualY,Plane.mix]
  module

theorem Plane.scaled_mix_bound (B : Plane E) (a x y : ℝ) {M : ℝ}
    (hM : 0 ≤ M) (h : 7000000^2*(x^2+y^2) ≤ M^2) :
    ‖(7000000:ℝ) • B.mix a x y‖ ≤ M := by
  have hs : ‖(7000000:ℝ) • B.mix a x y‖^2 = 7000000^2*(x^2+y^2) := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,B.mix_norm_sq]
  nlinarith [norm_nonneg ((7000000:ℝ) • B.mix a x y)]

/-- Scalar polynomial bounds imply physical prediction bounds throughout
the burn. This is the common final theorem for either parameter algebra. -/
theorem PositionCurve.error_bound (P : PositionCurve) (B : Plane E) {θ M d : ℝ}
    (X : PhysicalDeviation B.reference (B.force θ))
    (hθ : |θ| ≤ 7/20) (hM : M < 7000000) (hactual : (Direct.tubeRadius:ℝ) ≤ M)
    (hlip : 360000*(2*mu/(7000000-M)^3) ≤ 17/20) (hd : 0 ≤ d)
    (hi : P.x 0 = 0 ∧ P.y 0 = 0 ∧ P.dx 0 = 0 ∧ P.dy 0 = 0)
    (hr : ∀ t ∈ Icc (0:ℝ) 1, 7000000^2*((P.x t)^2+(P.y t)^2) ≤ M^2)
    (hres : ∀ t ∈ Icc (0:ℝ) 1, (P.residualX θ t)^2+(P.residualY θ t)^2 ≤ d^2) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖X.p t-P.position B t‖ ≤ (Direct.positionGain:ℝ)*
        (7000000*d+360000*(4*mu/(7000000-M)^5)*M^3) ∧
      ‖X.v t-P.velocity B t‖/600 ≤ (Direct.velocityGain:ℝ)/600*
        (7000000*d+360000*(4*mu/(7000000-M)^5)*M^3) := by
  have hR : (0:ℚ) < Direct.tubeRadius :=
    lt_trans (by norm_num) Direct.numerical_enclosures.2.2.1
  have hMn : 0 ≤ M := (show (0:ℝ) ≤ Direct.tubeRadius by exact_mod_cast hR.le).trans hactual
  apply X.numerical_prediction (P.position B) (P.velocity B) (P.acceleration B)
    hM hactual hlip (by positivity)
  · intro t _
    exact (B.reference_norm t).ge
  · intro t _
    have h := (B.force_norm θ t).trans
      (mul_le_mul_of_nonneg_left hθ (le_of_lt (lt_trans (by norm_num) thrust_bounds.1)))
    simpa only [thrust_bounds.2.1] using h
  · exact continuous_iff_continuousAt.mpr (fun t => (P.position_derivative B t).continuousAt)
  · exact continuous_iff_continuousAt.mpr (fun t => (P.velocity_derivative B t).continuousAt)
  · exact fun t _ => P.position_derivative B t
  · exact fun t _ => P.velocity_derivative B t
  · simp [PositionCurve.position,Plane.mix,hi.1,hi.2.1]
  · simp [PositionCurve.velocity,Plane.mix,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]
  · intro t ht
    exact B.scaled_mix_bound (rate*t) (P.x t) (P.y t) hMn (hr t ht)
  · intro t ht
    rw [P.physical_residual]
    apply B.scaled_mix_bound _ _ _ (by positivity)
    nlinarith [hres t ht]

end GNC.OrbitalComparison.PoweredCircle
