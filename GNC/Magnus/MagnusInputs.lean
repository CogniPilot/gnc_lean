import GNC.Magnus.MagnusAlgebra

/-! FOH increment bias derivatives and the uniform-slope coning stencil. -/
noncomputable section
namespace GNC.Magnus
open Matrix

def rotationIncrement (h : ℝ) (ω dω : Vec3) : Vec3 :=
  h • (ω + (1/2:ℝ) • dω) + (h^2/12) • crossProduct ω dω

def velocityIncrement (h : ℝ) (ω a dω da : Vec3) : Vec3 :=
  h • (a + (1/2:ℝ) • da) + (h^2/12) •
    (crossProduct ω da - crossProduct dω a)

def positionIncrement (h : ℝ) (da : Vec3) : Vec3 := -(h^2/12) • da

/-- Eq. (21), first as an exact affine bias identity. -/
theorem rotation_bias_affine (h : ℝ) (ω dω b : Vec3) :
    rotationIncrement h (ω-b) dω = rotationIncrement h ω dω +
      (-h) • b + (h^2/12) • crossProduct dω b := by
  ext i; fin_cases i <;> simp [rotationIncrement, crossProduct, vecHead, vecTail] <;> ring

/-- Eqs. (22)--(23), including both gyro and accelerometer bias. -/
theorem velocity_bias_affine (h : ℝ) (ω a dω da bg ba : Vec3) :
    velocityIncrement h (ω-bg) (a-ba) dω da = velocityIncrement h ω a dω da +
      (-h) • ba + (h^2/12) • (crossProduct da bg + crossProduct dω ba) := by
  ext i; fin_cases i <;> simp [velocityIncrement, crossProduct, vecHead, vecTail] <;> ring

theorem rotation_bias_derivative (h : ℝ) (ω dω b : Vec3) :
    HasDerivAt (fun s : ℝ => rotationIncrement h (ω-s • b) dω)
      ((-h) • b + (h^2/12) • crossProduct dω b) 0 := by
  have he : (fun s : ℝ => rotationIncrement h (ω-s • b) dω) =
      fun s => rotationIncrement h ω dω +
        s • ((-h) • b + (h^2/12) • crossProduct dω b) := by
    funext s; rw [rotation_bias_affine]
    ext i; fin_cases i <;> simp [crossProduct, vecHead, vecTail] <;> ring
  rw [he]
  simpa only [one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const
    ((-h) • b + (h^2/12) • crossProduct dω b)).const_add (rotationIncrement h ω dω)

theorem velocity_bias_derivative (h : ℝ) (ω a dω da bg ba : Vec3) :
    HasDerivAt (fun s : ℝ => velocityIncrement h (ω-s • bg) (a-s • ba) dω da)
      ((-h) • ba + (h^2/12) • (crossProduct da bg + crossProduct dω ba)) 0 := by
  have he : (fun s : ℝ => velocityIncrement h (ω-s • bg) (a-s • ba) dω da) =
      fun s => velocityIncrement h ω a dω da +
        s • ((-h) • ba + (h^2/12) • (crossProduct da bg + crossProduct dω ba)) := by
    funext s; rw [velocity_bias_affine]
    ext i; fin_cases i <;> simp [crossProduct, vecHead, vecTail] <;> ring
  rw [he]
  simpa only [one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const
    ((-h) • ba + (h^2/12) • (crossProduct da bg + crossProduct dω ba))).const_add
      (velocityIncrement h ω a dω da)

/-- Proposition 9: exact equality for uniform slope. An error bound for
nonuniform sampled input is a separate interpolation obligation. -/
theorem uniform_coning_stencil (h : ℝ) (ω d : Vec3) :
    (1/12:ℝ) • crossProduct ((h/2) • ((2:ℝ) • ω-d))
      ((h/2) • ((2:ℝ) • ω+d)) = (h^2/12) • crossProduct ω d := by
  ext i; fin_cases i <;> simp [crossProduct] <;> ring

/-- Proposition 7: centered first and second differences cancel a constant
bias, for vector-valued data as well as scalar data. -/
theorem centered_bias_invariant (h : ℝ) (prev now next b : Vec3) :
    (2*h)⁻¹ • ((next-b)-(prev-b)) = (2*h)⁻¹ • (next-prev) ∧
    (2*h^2)⁻¹ • ((next-b)-(2:ℝ) • (now-b)+(prev-b)) =
      (2*h^2)⁻¹ • (next-(2:ℝ) • now+prev) := by
  constructor <;> congr 1 <;> ext i <;> simp <;> ring

end GNC.Magnus
