import GNC.Applications.OrbitalComparison.SpatialPointing
import GNC.Applications.OrbitalComparison.UniformCertificate

/-! Physical three-dimensional burn laws for the common certificate.
The rational orthogonal change of axis makes the pointing axis oblique to
the orbital plane. RTN here is the prescribed reference frame.
-/
noncomputable section
set_option maxHeartbeats 0
namespace GNC.OrbitalComparison.SpatialBurn
open Matrix Real
open scoped Matrix

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def e0 : E3 := WithLp.toLp 2 ![1,0,0]
def e1 : E3 := WithLp.toLp 2 ![0,1,0]
def e2 : E3 := WithLp.toLp 2 ![0,0,1]
def pack (x y z : ℝ) : E3 := x • e0+y • e1+z • e2

theorem pack_eq (x y z : ℝ) : pack x y z = WithLp.toLp 2 ![x,y,z] := by
  ext i
  fin_cases i <;> simp [pack,e0,e1,e2]

theorem pack_norm_sq (x y z : ℝ) : ‖pack x y z‖^2 = x^2+y^2+z^2 := by
  rw [pack_eq]
  exact enorm_sq ![x,y,z]

theorem pack_norm_le (x y z : ℝ) : ‖pack x y z‖ ≤ |x|+|y|+|z| := by
  have h := pack_norm_sq x y z
  have hxy := mul_nonneg (abs_nonneg x) (abs_nonneg y)
  have hxz := mul_nonneg (abs_nonneg x) (abs_nonneg z)
  have hyz := mul_nonneg (abs_nonneg y) (abs_nonneg z)
  nlinarith [norm_nonneg (pack x y z),sq_abs x,sq_abs y,sq_abs z,
    abs_nonneg x,abs_nonneg y,abs_nonneg z]

def axisFrameMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,0,0;0,4/5,-3/5;0,3/5,4/5]

def axisFrame : SO3 := by
  refine ⟨axisFrameMatrix,?_,?_⟩
  · apply (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [axisFrameMatrix,mul_apply,Fin.sum_univ_succ]
  · norm_num [axisFrameMatrix,det_fin_three,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

def attitude (θ : ℝ) : SO3 := axisFrame*AxisRotation.zRotation θ*axisFrame⁻¹

theorem axisFrame_inverse : (axisFrame⁻¹).val = axisFrameMatrix.transpose := by
  rfl

@[simp] theorem attitude_matrix (θ : ℝ) :
    (attitude θ).val = axisFrameMatrix*AxisRotation.zMatrix θ*axisFrameMatrix.transpose := by
  change axisFrame.val*(AxisRotation.zRotation θ).val*(axisFrame⁻¹).val = _
  rw [axisFrame_inverse]
  rfl

theorem oblique_axis : rotate axisFrame ![0,0,1] = ![0,-3/5,4/5] := by
  ext i
  fin_cases i <;> norm_num [rotate,axisFrame,axisFrameMatrix,mulVec,dotProduct,Fin.sum_univ_succ]

inductive Law where
  | rtnReferenceOffset
  | rtnInertialOffset
  | inertiallyFixed
  deriving DecidableEq

def direction (mode : Law) (θ phase : ℝ) : Vec3 :=
  match mode with
  | .rtnReferenceOffset => rotate (AxisRotation.zRotation phase*attitude θ) ![1,0,0]
  | .rtnInertialOffset => rotate (attitude θ*AxisRotation.zRotation phase) ![1,0,0]
  | .inertiallyFixed => rotate (attitude θ) ![1,0,0]

/-- Algebraic source map; c=cos(theta), s=sin(theta), C=cos(phase), S=sin(phase). -/
def components (mode : Law) (c s C S : ℝ) : Vec3 :=
  match mode with
  | .rtnReferenceOffset => ![C*c-(4/5)*S*s,S*c+(4/5)*C*s,(3/5)*s]
  | .rtnInertialOffset =>
    ![C*c-(4/5)*S*s,(4/5)*C*s+S-(16/25)*S*(1-c),
      (3/5)*C*s-(12/25)*S*(1-c)]
  | .inertiallyFixed => ![c,(4/5)*s,(3/5)*s]

theorem direction_components (mode : Law) (θ phase : ℝ) :
    direction mode θ phase = components mode (cos θ) (sin θ) (cos phase) (sin phase) := by
  cases mode <;> ext i <;> fin_cases i <;>
    simp [direction,components,rotate,axisFrameMatrix,
      AxisRotation.zRotation,AxisRotation.zMatrix,mulVec,mul_apply,dotProduct,
      Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem direction_unit (mode : Law) (θ phase : ℝ) : enorm (direction mode θ phase) = 1 := by
  cases mode <;> simp only [direction,rotate_enorm]
  all_goals
    have h := enorm_sq (![1,0,0] : Vec3)
    change enorm (![1,0,0] : Vec3)^2 = (1:ℝ)^2+0^2+0^2 at h
    nlinarith [enorm_nonneg (![1,0,0] : Vec3)]

def source (mode : Law) (θ t : ℝ) : E3 :=
  WithLp.toLp 2 (direction mode θ ((UniformCertificate.omega:ℝ)*t))

theorem source_components (mode : Law) (θ t : ℝ) :
    source mode θ t =
      pack ((components mode (cos θ) (sin θ) (cos ((UniformCertificate.omega:ℝ)*t))
        (sin ((UniformCertificate.omega:ℝ)*t))) 0)
      ((components mode (cos θ) (sin θ) (cos ((UniformCertificate.omega:ℝ)*t))
        (sin ((UniformCertificate.omega:ℝ)*t))) 1)
      ((components mode (cos θ) (sin θ) (cos ((UniformCertificate.omega:ℝ)*t))
        (sin ((UniformCertificate.omega:ℝ)*t))) 2) := by
  rw [source,direction_components,pack_eq]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem source_unit (mode : Law) (θ t : ℝ) : ‖source mode θ t‖ = 1 :=
  direction_unit mode θ _

/-- The two RTN offset conventions have the same nominal. The inertial
nominal source is constant, so its physical nominal must be propagated separately. -/
theorem nominal_sources (t : ℝ) :
    source .rtnReferenceOffset 0 t =
      pack (cos ((UniformCertificate.omega:ℝ)*t)) (sin ((UniformCertificate.omega:ℝ)*t)) 0 ∧
    source .rtnInertialOffset 0 t = source .rtnReferenceOffset 0 t ∧
    source .inertiallyFixed 0 t = e0 := by
  simp [source_components,components,pack]

end GNC.OrbitalComparison.SpatialBurn
