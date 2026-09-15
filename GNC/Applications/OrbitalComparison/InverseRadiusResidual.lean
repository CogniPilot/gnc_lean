import GNC.Applications.OrbitalComparison.WeightedCertificate
import GNC.Dynamics.InverseRadius

/-! Full inverse-square differential defects in the physical rotating frame.
A proposed dimensionless inverse radius 1+e is checked by its polynomial
algebraic constraint. This retains cancellations across all gravity orders.
-/
noncomputable section
namespace GNC.OrbitalComparison.PoweredCircle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def inverseCubic (e : ℝ) : ℝ := 3*e+3*e^2+e^3

def inverseConstraint (x y e : ℝ) : ℝ :=
  (2*x+x^2+y^2)+(2*e+e^2)+(2*x+x^2+y^2)*(2*e+e^2)

def inverseAmplitude (M b : ℝ) : ℝ := ((7000000+M)/7000000)*(1+b)
def inverseGain (M b : ℝ) : ℝ :=
  360000*mu*Gravity.inverseRadiusFactor (inverseAmplitude M b)/(7000000-M)^2

def Plane.liftedAcceleration (B : Plane E) (θ t x y e : ℝ) : E :=
  (360000:ℝ) • ((-mu*((1+e)/7000000)^3) •
    (B.reference t+(7000000:ℝ) • B.mix (rate*t) x y)-Gravity.field mu (B.reference t)+B.force θ t)

theorem Plane.lifted_components (B : Plane E) (θ t x y e : ℝ) :
    B.liftedAcceleration θ t x y e =
      (7000000:ℝ) • B.mix (rate*t)
        (-gradientScale*(x+(1+x)*inverseCubic e)-forceScale*(1-Real.cos θ))
        (-gradientScale*(y+y*inverseCubic e)+forceScale*Real.sin θ) := by
  unfold Plane.liftedAcceleration
  rw [Gravity.field,B.reference_norm,B.force_decomposition]
  dsimp [Plane.reference,Plane.mix,Plane.sineForce,Plane.cosineForce,
    gradientScale,forceScale,inverseCubic]
  module

def PositionCurve.fullResidualX (P : PositionCurve) (θ t e : ℝ) : ℝ :=
  P.ddx t-2*rate*P.dy t-rate^2*P.x t+
    gradientScale*(P.x t+(1+P.x t)*inverseCubic e)+forceScale*(1-Real.cos θ)
def PositionCurve.fullResidualY (P : PositionCurve) (θ t e : ℝ) : ℝ :=
  P.ddy t+2*rate*P.dx t-rate^2*P.y t+
    gradientScale*(P.y t+P.y t*inverseCubic e)-forceScale*Real.sin θ

theorem PositionCurve.full_residual (P : PositionCurve) (B : Plane E) (θ t e : ℝ) :
    P.acceleration B t-B.liftedAcceleration θ t (P.x t) (P.y t) e =
      (7000000:ℝ) • B.mix (rate*t) (P.fullResidualX θ t e) (P.fullResidualY θ t e) := by
  rw [B.lifted_components]
  dsimp [PositionCurve.acceleration,PositionCurve.fullResidualX,PositionCurve.fullResidualY,Plane.mix]
  module

theorem Plane.shifted_norm_sq (B : Plane E) (t x y : ℝ) :
    ‖B.reference t+(7000000:ℝ) • B.mix (rate*t) x y‖^2 =
      7000000^2*((1+x)^2+y^2) := by
  have he : B.reference t+(7000000:ℝ) • B.mix (rate*t) x y =
      (7000000:ℝ) • B.mix (rate*t) (1+x) y := by
    dsimp [Plane.reference,Plane.mix]
    module
  rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,B.mix_norm_sq]

theorem Plane.inverse_constraint (B : Plane E) (t x y e : ℝ) :
    ‖B.reference t+(7000000:ℝ) • B.mix (rate*t) x y‖^2*((1+e)/7000000)^2-1 =
      inverseConstraint x y e := by
  rw [B.shifted_norm_sq]
  unfold inverseConstraint
  ring

/-- Converts the complete polynomial lift defect into a physical gravity
error, using the same certified candidate radius as the trajectory theorem. -/
theorem Plane.lift_difference (B : Plane E) (θ t x y e : ℝ) {M b : ℝ}
    (hM : M < 7000000) (hp : ‖(7000000:ℝ) • B.mix (rate*t) x y‖ ≤ M)
    (hb : b < 1) (he : |e| ≤ b) :
    ‖B.liftedAcceleration θ t x y e-
      nonlinearAcceleration (B.reference t) ((7000000:ℝ) • B.mix (rate*t) x y) (B.force θ t)‖ ≤
      inverseGain M b*|inverseConstraint x y e| := by
  let p := (7000000:ℝ) • B.mix (rate*t) x y
  have hMn : 0 ≤ M := (norm_nonneg _).trans hp
  have helo := (abs_le.mp he).1
  have hehi := (abs_le.mp he).2
  have hu : 0 ≤ (1+e)/7000000 := div_nonneg (by linarith) (by norm_num)
  have hm : 0 < 7000000-M := sub_pos.mpr hM
  have hr : 7000000-M ≤ ‖B.reference t+p‖ := by
    have hn := norm_add_le (B.reference t+p) (-p)
    simp only [add_neg_cancel_right,norm_neg,B.reference_norm] at hn
    dsimp [p] at *
    linarith
  have hupper : ‖B.reference t+p‖ ≤ 7000000+M := by
    exact (norm_add_le _ _).trans (by simpa only [B.reference_norm] using add_le_add_right hp 7000000)
  have hA : ‖B.reference t+p‖*((1+e)/7000000) ≤ inverseAmplitude M b := by
    have hh := mul_le_mul hupper (show (1+e)/7000000 ≤ (1+b)/7000000 by linarith)
      hu (by positivity : 0 ≤ (7000000:ℝ)+M)
    convert hh using 1 <;> unfold inverseAmplitude <;> ring
  have hg := Gravity.field_inverse_radius_bound mu (by norm_num [mu]) (B.reference t+p) hm hr hu hA
  have hd : B.liftedAcceleration θ t x y e-
      nonlinearAcceleration (B.reference t) p (B.force θ t) =
      (360000:ℝ) • ((-mu*((1+e)/7000000)^3) • (B.reference t+p)-Gravity.field mu (B.reference t+p)) := by
    dsimp [Plane.liftedAcceleration,nonlinearAcceleration,p]
    module
  change ‖B.liftedAcceleration θ t x y e-nonlinearAcceleration (B.reference t) p (B.force θ t)‖ ≤ _
  rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 360000),norm_sub_rev]
  have hh := mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 360000)
  dsimp [p] at hh
  rw [B.inverse_constraint] at hh
  convert hh using 1 <;> unfold inverseGain <;> ring

end GNC.OrbitalComparison.PoweredCircle
