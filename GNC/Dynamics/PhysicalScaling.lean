import GNC.Dynamics.GravityGeometry
import GNC.Dynamics.GravityLinearization

/-! Exact conversion from normalized inverse-square dynamics to physical
position, velocity and force. Positive length/time/mass scales are explicit;
there is no rounded unit conversion or neglected mass factor.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.PhysicalScaling

def position (length timeScale : ℝ) (p : ℝ → Vec3) (s : ℝ) : Vec3 :=
  length • p (s/timeScale)

def velocity (length timeScale : ℝ) (v : ℝ → Vec3) (s : ℝ) : Vec3 :=
  (length/timeScale) • v (s/timeScale)

theorem gravity (μ length : ℝ) (hL : 0 < length) (p : Vec3) :
    Gravity.field3 μ (length • p) = (μ/length^2) • Gravity.field3 1 p := by
  have h := Gravity.field_positive_scale μ length hL (WithLp.toLp 2 p : Jacobian.E3)
  rw [Gravity.field_parameter μ (WithLp.toLp 2 p : Jacobian.E3)] at h
  have h' := congrArg WithLp.ofLp h
  change Gravity.field3 μ (length • p) = (1/length^2) • (μ • Gravity.field3 1 p) at h'
  rw [smul_smul] at h'
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using h'

theorem position_derivative {length timeScale s : ℝ} {p : ℝ → Vec3} {v : Vec3}
    (hp : HasDerivAt p v (s/timeScale)) :
    HasDerivAt (position length timeScale p) ((length/timeScale) • v) s := by
  have h := (hp.scomp s ((hasDerivAt_id s).div_const timeScale)).const_smul length
  convert h using 1
  simp [smul_smul,div_eq_mul_inv]

theorem velocity_derivative {μ length timeScale s : ℝ} {v : ℝ → Vec3} {p a : Vec3}
    (hL : 0 < length) (hscale : μ/length^2 = length/timeScale^2)
    (hv : HasDerivAt v (Gravity.field3 1 p+a) (s/timeScale)) :
    HasDerivAt (velocity length timeScale v)
      (Gravity.field3 μ (length • p)+(length/timeScale^2) • a) s := by
  have h := (hv.scomp s ((hasDerivAt_id s).div_const timeScale)).const_smul (length/timeScale)
  convert h using 1
  rw [gravity μ length hL,hscale]
  simp only [smul_smul,smul_add]
  have he : length/timeScale*(1/timeScale) = length/timeScale^2 := by ring
  rw [he]

theorem force_recovers_acceleration (m : ℝ) (hm : m ≠ 0) (a : Vec3) :
    m⁻¹ • (m • a) = a := by rw [smul_smul,inv_mul_cancel₀ hm,one_smul]

theorem position_nonzero {length timeScale s : ℝ} {p : ℝ → Vec3}
    (hL : length ≠ 0) (hp : p (s/timeScale) ≠ 0) : position length timeScale p s ≠ 0 :=
  smul_ne_zero hL hp

end GNC.PhysicalScaling
