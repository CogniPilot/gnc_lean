import GNC.Dynamics.MatrixDynamics
import GNC.Dynamics.MixedLogLinear
import GNC.Dynamics.GravityLinearization

/-! The exact group-affinity test for spacecraft kinematics on SE2(3).
All inputs can depend on time: the algebraic test is at each fixed time.
Only the gravitational field enters its defect. Uniform and isotropic affine
gravity give state-independent ambient mixed coefficients, even with varying
acceleration, angular rate, and gravitational coefficient.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
namespace GNC.SpacecraftGroupAffinity
open Matrix
open scoped Matrix.Norms.Operator

def V (g : Vec3) : Mat5 := hat (velocityOnly g)

theorem V_add (g h : Vec3) : V (g+h)=V g+V h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [V,hat,velocityOnly]

theorem V_sub (g h : Vec3) : V (g-h)=V g-V h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [V,hat,velocityOnly]

theorem V_zero : V 0=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [V,hat,velocityOnly]

theorem V_injective : Function.Injective V := by
  intro g h he
  have hv := hat_injective he
  exact congrFun hv 1

theorem V_right (X : SE23) (g : Vec3) : V g*X.toMatrix=V g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V,hat,velocityOnly,SE23.toMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

theorem V_left (X : SE23) (g : Vec3) : X.toMatrix*V g=V (rotate X.rot g) := by
  rw [show X.toMatrix*V g=V (rotate X.rot g)*X.toMatrix from gravity_intertwine X g,
    V_right]

def field (g : Vec3 → Vec3) (ν : LogState) (X : SE23) : Mat5 :=
  spacecraftDerivative X ν (g X.pos)

theorem field_form (g : Vec3 → Vec3) (ν : LogState) (X : SE23) :
    field g ν X=V (g X.pos)-kinematicC*X.toMatrix+X.toMatrix*(hat ν+kinematicC) := by
  change (V (g X.pos)-kinematicC)*X.toMatrix+X.toMatrix*(hat ν+kinematicC)=_
  rw [sub_mul,V_right]

/-- This defect measures failure of the group law, not failure to be
constant in time or linear in ambient Cartesian state coordinates. -/
def gravityDefect (g : Vec3 → Vec3) (X Y : SE23) : Vec3 :=
  g (X.pos+rotate X.rot Y.pos)-g X.pos-rotate X.rot (g Y.pos)+rotate X.rot (g 0)

theorem matrix_defect (g : Vec3 → Vec3) (ν : LogState) (X Y : SE23) :
    field g ν (X*Y)-field g ν X*Y.toMatrix-X.toMatrix*field g ν Y+
      X.toMatrix*field g ν 1*Y.toMatrix=V (gravityDefect g X Y) := by
  simp only [field_form,SE23.toMatrix_mul,SE23.toMatrix_one,SE23.one_pos,
    SE23.mul_pos,gravityDefect,V_add,V_sub,mul_one,one_mul,
    add_mul,sub_mul,mul_add,mul_sub,V_right,V_left]
  noncomm_ring

/-- Exact necessary and sufficient condition for the usual matrix
group-affinity identity on SE2(3). Tangency is supplied by spacecraft
kinematics; this statement tests its matrix identity directly. -/
theorem group_affine_iff (g : Vec3 → Vec3) (ν : LogState) :
    (∀ X Y : SE23, field g ν (X*Y)=field g ν X*Y.toMatrix+
      X.toMatrix*field g ν Y-X.toMatrix*field g ν 1*Y.toMatrix) ↔
    ∀ X Y : SE23, gravityDefect g X Y=0 := by
  constructor
  · intro h X Y
    apply V_injective
    rw [←matrix_defect g ν X Y,h,V_zero]
    abel
  · intro h X Y
    have he := matrix_defect g ν X Y
    rw [h,V_zero] at he
    apply sub_eq_zero.mp
    convert he using 1; abel

theorem affine_defect (L : Vec3 →ₗ[ℝ] Vec3) (b : Vec3) (X Y : SE23) :
    gravityDefect (fun p => L p+b) X Y=
      L (rotate X.rot Y.pos)-rotate X.rot (L Y.pos) := by
  simp only [gravityDefect,map_add,map_zero,zero_add,rotate_add]
  module

theorem isotropic_defect (k : ℝ) (b : Vec3) (X Y : SE23) :
    gravityDefect (fun p => k • p+b) X Y=0 := by
  simp only [gravityDefect,rotate_add,rotate_smul,smul_add,smul_zero,zero_add]
  module

/-- No time regularity or constancy restriction is needed for the
pointwise group-affinity identity. Regularity for ODE existence is separate. -/
theorem time_varying_group_affine (k : ℝ → ℝ) (b : ℝ → Vec3)
    (ν : ℝ → LogState) (t : ℝ) :
    ∀ X Y : SE23, field (fun p => k t • p+b t) (ν t) (X*Y)=
      field (fun p => k t • p+b t) (ν t) X*Y.toMatrix+
      X.toMatrix*field (fun p => k t • p+b t) (ν t) Y-
      X.toMatrix*field (fun p => k t • p+b t) (ν t) 1*Y.toMatrix :=
  (group_affine_iff _ _).mpr (isotropic_defect (k t) (b t))

def coupling (k : ℝ) : Mat5 := Matrix.single 4 3 k
def leftCoefficient (k : ℝ) (b : Vec3) : Mat5 := V b-kinematicC-coupling k
def rightCoefficient (k : ℝ) (ν : LogState) : Mat5 := hat ν+kinematicC+coupling k

theorem coupling_commutator (k : ℝ) (X : SE23) :
    X.toMatrix*coupling k-coupling k*X.toMatrix=V (k • X.pos) := by
  ext i j
  simp only [coupling,Matrix.sub_apply,Matrix.mul_apply,Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply,V,hat,velocityOnly,SE23.toMatrix,mul_comm]

/-- An explicit ambient mixed-invariant representation of isotropic
affine gravity. Neither coefficient depends on the spacecraft state. -/
theorem isotropic_mixed (k : ℝ) (b : Vec3) (ν : LogState) (X : SE23) :
    field (fun p => k • p+b) ν X=
      leftCoefficient k b*X.toMatrix+X.toMatrix*rightCoefficient k ν := by
  rw [field_form]
  rw [V_add, ←coupling_commutator]
  simp only [leftCoefficient,rightCoefficient,sub_mul,mul_add,V_right]
  noncomm_ring

end GNC.SpacecraftGroupAffinity
