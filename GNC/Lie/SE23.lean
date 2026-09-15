import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Tactic

/-! The group and matrix Lie algebra used in equations (1), (3), (8), and (47).

SO(3), the ambient general linear Lie group, and the Lie-subalgebra machinery
come from mathlib. We do not claim here to construct manifold charts on SE₂(3)
or to identify this matrix Lie algebra with its manifold tangent Lie algebra.
-/

noncomputable section
open Matrix
open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

namespace GNC

abbrev Vec3 := Fin 3 → ℝ
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ
abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℝ

/-- The paper's rotation action, reusing mathlib's special orthogonal group. -/
def rotate (R : SO3) (v : Vec3) : Vec3 := (R : Matrix _ _ ℝ) *ᵥ v

@[simp] theorem rotate_one (v : Vec3) : rotate 1 v = v := by simp [rotate]
@[simp] theorem rotate_zero (R : SO3) : rotate R 0 = 0 := by simp [rotate]
@[simp] theorem rotate_add (R : SO3) (u v : Vec3) :
    rotate R (u + v) = rotate R u + rotate R v := by simp [rotate, mulVec_add]
@[simp] theorem rotate_neg (R : SO3) (v : Vec3) : rotate R (-v) = -rotate R v := by
  simp [rotate, Matrix.mulVec_neg]
@[simp] theorem rotate_sub (R : SO3) (u v : Vec3) :
    rotate R (u - v) = rotate R u - rotate R v := by simp [rotate, mulVec_sub]
theorem rotate_mul (R S : SO3) (v : Vec3) :
    rotate (R * S) v = rotate R (rotate S v) := by simp [rotate, mulVec_mulVec]

/-- Double direct spatial isometries, in the paper's (R,v,p) convention. -/
@[ext] structure SE23 where
  rot : SO3
  vel : Vec3
  pos : Vec3

namespace SE23

instance : Mul SE23 := ⟨fun X Y =>
  ⟨X.rot * Y.rot, X.vel + rotate X.rot Y.vel, X.pos + rotate X.rot Y.pos⟩⟩
instance : One SE23 := ⟨⟨1, 0, 0⟩⟩
instance : Inv SE23 := ⟨fun X =>
  ⟨X.rot⁻¹, -rotate X.rot⁻¹ X.vel, -rotate X.rot⁻¹ X.pos⟩⟩

@[simp] theorem mul_rot (X Y : SE23) : (X * Y).rot = X.rot * Y.rot := rfl
@[simp] theorem mul_vel (X Y : SE23) : (X * Y).vel = X.vel + rotate X.rot Y.vel := rfl
@[simp] theorem mul_pos (X Y : SE23) : (X * Y).pos = X.pos + rotate X.rot Y.pos := rfl
@[simp] theorem one_rot : (1 : SE23).rot = 1 := rfl
@[simp] theorem one_vel : (1 : SE23).vel = 0 := rfl
@[simp] theorem one_pos : (1 : SE23).pos = 0 := rfl
@[simp] theorem inv_rot (X : SE23) : X⁻¹.rot = X.rot⁻¹ := rfl
@[simp] theorem inv_vel (X : SE23) : X⁻¹.vel = -rotate X.rot⁻¹ X.vel := rfl
@[simp] theorem inv_pos (X : SE23) : X⁻¹.pos = -rotate X.rot⁻¹ X.pos := rfl

instance : Group SE23 where
  mul_assoc X Y Z := by ext <;> simp [mul_assoc, rotate_mul, add_assoc]
  one_mul X := by ext <;> simp
  mul_one X := by ext <;> simp
  inv_mul_cancel X := by ext <;> simp

/-- Left-invariant error (8). -/
def error (chief deputy : SE23) : SE23 := chief⁻¹ * deputy

theorem error_left_invariant (F chief deputy : SE23) :
    error (F * chief) (F * deputy) = error chief deputy := by
  simp [error, mul_assoc]

theorem error_pos (chief deputy : SE23) :
    (error chief deputy).pos = rotate chief.rot⁻¹ (deputy.pos - chief.pos) := by
  simp [error]; abel

theorem error_vel (chief deputy : SE23) :
    (error chief deputy).vel = rotate chief.rot⁻¹ (deputy.vel - chief.vel) := by
  simp [error]; abel

/-- Instantaneous inertial velocity jump; position and attitude are unchanged. -/
def impulse (X : SE23) (dv : Vec3) : SE23 := { X with vel := X.vel + dv }

theorem impulse_error (chief deputy : SE23) (dv : Vec3) :
    (error chief (impulse deputy dv)).pos = (error chief deputy).pos ∧
    (error chief (impulse deputy dv)).rot = (error chief deputy).rot ∧
    (error chief (impulse deputy dv)).vel =
      (error chief deputy).vel + rotate chief.rot⁻¹ dv := by
  simp [error, impulse, add_assoc]

/-- Equation (1), with column order (R,v,p). -/
def toMatrix (X : SE23) : Mat5 :=
  !![X.rot.1 0 0, X.rot.1 0 1, X.rot.1 0 2, X.vel 0, X.pos 0;
     X.rot.1 1 0, X.rot.1 1 1, X.rot.1 1 2, X.vel 1, X.pos 1;
     X.rot.1 2 0, X.rot.1 2 1, X.rot.1 2 2, X.vel 2, X.pos 2;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

@[simp] theorem toMatrix_one : toMatrix 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMatrix]

theorem toMatrix_mul (X Y : SE23) : toMatrix (X * Y) = toMatrix X * toMatrix Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, rotate, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

def matrixHom : SE23 →* Mat5 where
  toFun := toMatrix
  map_one' := toMatrix_one
  map_mul' := toMatrix_mul

/-- The group embeds into the ambient general linear Lie group. -/
def matrixUnits : SE23 →* Mat5ˣ := matrixHom.toHomUnits

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro X Y h
  have he : ∀ i j, toMatrix X i j = toMatrix Y i j := fun i j => congrFun (congrFun h i) j
  apply SE23.ext
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> first
      | exact he 0 0 | exact he 0 1 | exact he 0 2
      | exact he 1 0 | exact he 1 1 | exact he 1 2
      | exact he 2 0 | exact he 2 1 | exact he 2 2
  · ext i; fin_cases i <;> first | exact he 0 3 | exact he 1 3 | exact he 2 3
  · ext i; fin_cases i <;> first | exact he 0 4 | exact he 1 4 | exact he 2 4

theorem matrixUnits_injective : Function.Injective matrixUnits := by
  intro X Y h
  exact toMatrix_injective (congrArg (fun U : Mat5ˣ => (U : Mat5)) h)

end SE23

/-- Coordinates ordered as (position, velocity, attitude), each with three entries. -/
abbrev LogState := Fin 3 → Vec3

/-- Equation (3), represented in the ambient 5 by 5 matrix algebra. -/
def hat (x : LogState) : Mat5 :=
  !![0, -x 2 2, x 2 1, x 1 0, x 0 0;
     x 2 2, 0, -x 2 0, x 1 1, x 0 1;
     -x 2 1, x 2 0, 0, x 1 2, x 0 2;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0]

def hatLinear : LogState →ₗ[ℝ] Mat5 where
  toFun := hat
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [hat, add_comm]
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> simp [hat]

/-- The inverse of hat on its range, in the same ordering. -/
def vee (A : Mat5) : LogState :=
  ![![A 0 4, A 1 4, A 2 4], ![A 0 3, A 1 3, A 2 3], ![A 2 1, A 0 2, A 1 0]]

@[simp] theorem vee_hat (x : LogState) : vee (hat x) = x := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem hat_injective : Function.Injective hat := Function.LeftInverse.injective vee_hat

/-- The coordinate adjoint of equation (47). -/
def ad (x y : LogState) : LogState :=
  ![x 2 ⨯₃ y 0 + x 0 ⨯₃ y 2,
    x 2 ⨯₃ y 1 + x 1 ⨯₃ y 2,
    x 2 ⨯₃ y 2]

/-- The coordinate bracket is exactly the existing matrix commutator. -/
theorem hat_ad (x y : LogState) : hat (ad x y) = ⁅hat x, hat y⁆ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hat, ad, cross_apply, Ring.lie_def] <;> ring

/-- A pure gravity mismatch has only a velocity block. -/
def velocityOnly (v : Vec3) : LogState := ![0, v, 0]

/-- The zero position–velocity block, needed in addition to upper triangularity
in Lemma 1, is preserved by the adjoint. -/
theorem ad_velocityOnly (x : LogState) (v : Vec3) :
    ad x (velocityOnly v) = velocityOnly (x 2 ⨯₃ v) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ad, velocityOnly]

/-- Every power used in the Jacobian series preserves the gravity block. -/
theorem iterate_ad_velocityOnly (x : LogState) (v : Vec3) (k : ℕ) :
    (ad x)^[k] (velocityOnly v) = velocityOnly ((fun u => x 2 ⨯₃ u)^[k] v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ad_velocityOnly, Function.iterate_succ_apply']

/-- se₂(3) as an actual mathlib Lie subalgebra, not an axiomatized bracket. -/
def se23 : LieSubalgebra ℝ Mat5 where
  __ := LinearMap.range hatLinear
  lie_mem' {a b} ha hb := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨ad x y, hat_ad x y⟩

example : LieRing se23 := inferInstance
example : LieAlgebra ℝ se23 := inferInstance

/-- Jacobi is inherited from mathlib's matrix Lie algebra. -/
theorem ad_jacobi (x y z : LogState) :
    ad x (ad y z) + ad y (ad z x) + ad z (ad x y) = 0 := by
  apply hat_injective
  change hatLinear _ = hatLinear _
  simp only [map_add, map_zero]
  simp only [hatLinear, LinearMap.coe_mk, AddHom.coe_mk, hat_ad]
  exact lie_jacobi (hat x) (hat y) (hat z)

/-- The kinematic matrix C in (6), which is outside se₂(3). -/
def kinematicC : Mat5 :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1; 0, 0, 0, 0, 0]

/-- The kinematic adjoint identity used in Proposition 1. -/
theorem hat_kinematic (x : LogState) :
    hat (![x 1, 0, 0]) = ⁅hat x, kinematicC⁆ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hat, kinematicC, Ring.lie_def]

/-- The ambient GL(5,ℝ) is a Lie group by mathlib's normed-algebra theorem. -/
example : LieGroup 𝓘(ℝ, Mat5) ∞ Mat5ˣ := inferInstance

end GNC
