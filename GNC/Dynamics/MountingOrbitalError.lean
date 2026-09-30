import GNC.Dynamics.MountingTransport
import GNC.Lie.RotationKinematics

/-! Near-linear orbital error for a constant body-fixed mounting offset.
The coordinates are derived from actual position/velocity ODEs and the
commanded frame. Phi is constant in that frame, unlike the left attitude
error of two matched-body-rate spacecraft. Both gravity and frame-transport
remainders are retained; time-varying prescribed a and omega are allowed.
-/
noncomputable section
namespace GNC.MountingOrbitalError
open Matrix Real

def coordinates (φ : Vec3) (R : SO3) (p v q w : Vec3) : LogState :=
  ![Jacobian.inverseAt φ (rotate R⁻¹ (p-q)),
    Jacobian.inverseAt φ (rotate R⁻¹ (v-w)),φ]

def linearPart (μ : ℝ) (R : SO3) (q a ω : Vec3) (x : LogState) : LogState :=
  ![-(ω ⨯₃ x 0)+x 1,
    -(ω ⨯₃ x 1)+OrbitalNearAffine.gradient μ R q (x 0)+x 2 ⨯₃ a,0]

def remainder (μ : ℝ) (R : SO3) (q ω : Vec3) (x : LogState) : LogState :=
  ![-MountingTransport.defect (x 2) ω (x 0),
    OrbitalNearAffine.residual μ R q x-MountingTransport.defect (x 2) ω (x 1),0]

theorem reconstruction (φ : Vec3) (hφ : enorm φ<2*π) (R : SO3) (p v q w : Vec3) :
    q+rotate R (Jacobian.leftAt φ (coordinates φ R p v q w 0))=p := by
  simp only [coordinates, Matrix.cons_val_zero, Jacobian.leftAt_inverseAt_all φ _ hφ,
    ←rotate_mul, mul_inv_cancel, rotate_one, add_sub_cancel]

/-- Derived from the full physical inverse-square ODE with actual thrust
R(t) Exp(phi) a(t), reference thrust R(t) a(t), and common initial frame.
No presumed log ODE, trajectory approximation or small-angle thrust is used. -/
theorem equation (μ : ℝ) (φ : Vec3) (hφ : enorm φ<2*π)
    {R : ℝ → SO3} {p v q w : ℝ → Vec3} {a ω : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew ω) t)
    (hp : HasDerivAt p (v t) t) (hq : HasDerivAt q (w t) t)
    (hv : HasDerivAt v (Gravity.field3 μ (p t)+rotate (R t) (rotate (rotationExp φ) a)) t)
    (hw : HasDerivAt w (Gravity.field3 μ (q t)+rotate (R t) a) t) :
    HasDerivAt (fun s => coordinates φ (R s) (p s) (v s) (q s) (w s))
      (linearPart μ (R t) (q t) a ω (coordinates φ (R t) (p t) (v t) (q t) (w t))+
        remainder μ (R t) (q t) ω (coordinates φ (R t) (p t) (v t) (q t) (w t))) t := by
  let d := fun s => rotate (R s)⁻¹ (p s-q s)
  let u := fun s => rotate (R s)⁻¹ (v s-w s)
  let g := rotate (R t)⁻¹ (Gravity.field3 μ (p t)-Gravity.field3 μ (q t))
  have hd : HasDerivAt d (-(ω ⨯₃ d t)+u t) t := by
    convert RotationKinematics.inverse_rotate_derivative hR (hp.sub hq) using 1
    dsimp [d,u]
    abel
  have hu : HasDerivAt u (-(ω ⨯₃ u t)+g+(rotate (rotationExp φ) a-a)) t := by
    convert RotationKinematics.inverse_rotate_derivative hR (hv.sub hw) using 1
    simp only [g, rotate_sub, rotate_add, ←rotate_mul, ←mul_assoc,
      inv_mul_cancel, one_mul, rotate_one]
    dsimp [u]
    abel
  obtain ⟨hρ,hν⟩ := MountingErrorCoordinates.equations φ hφ hd hu
  let x := coordinates φ (R t) (p t) (v t) (q t) (w t)
  have hg : Jacobian.inverseAt φ g=
      OrbitalNearAffine.gradient μ (R t) (q t) (x 0)+
        OrbitalNearAffine.residual μ (R t) (q t) x := by
    have he := reconstruction φ hφ (R t) (p t) (v t) (q t) (w t)
    change q t+rotate (R t) (Jacobian.leftAt φ (x 0))=p t at he
    simp only [OrbitalNearAffine.residual, show x 2=φ from rfl, he, g]
    abel
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hρ using 1
    dsimp [coordinates, linearPart, remainder, MountingTransport.defect, d, u]
    module
  · convert hν using 1
    change _= _+Jacobian.inverseAt φ g+_
    rw [hg]
    dsimp [linearPart, remainder, MountingTransport.defect, x, coordinates, d, u]
    module
  · simpa [coordinates, linearPart, remainder] using hasDerivAt_const t φ

end GNC.MountingOrbitalError
