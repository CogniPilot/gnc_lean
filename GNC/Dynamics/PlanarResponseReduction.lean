import GNC.Dynamics.GravityLinearization
import GNC.Planning.FlopKernel

/-! Sparse variational kernels for a planar nominal thrust history.
The geometric response has four active position coefficients; the exact
Cartesian component response has ten. Both exploit the same planar gravity
block and symmetry. Their retained force responses differ; a geometric
physical certificate must still charge the Jacobian/gravity commutator.
The operation counts concern these kernels with prepared G and u, not a
minimum complexity theorem or a cost for the complete validated solver.
-/
noncomputable section
namespace GNC.PlanarResponseReduction
set_option autoImplicit false
open Matrix

def gravity (g : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![g 0,g 1,0; g 1,g 2,0; 0,0,g 3]

def gravityParameters (μ x y : ℝ) : Fin 4 → ℝ :=
  let r := enorm (![x,y,0] : Vec3)
  ![3*μ*x^2/r^5-μ/r^3, 3*μ*x*y/r^5, 3*μ*y^2/r^5-μ/r^3, -μ/r^3]

/-- The sparse symmetric block is the full reference gravity gradient. -/
theorem physical_gravity (μ x y : ℝ) (v : Vec3) :
    gravity (gravityParameters μ x y) *ᵥ v=Gravity.gradient3 μ ![x,y,0] v := by
  have hi := Gravity.inner_toLp (![x,y,0] : Vec3) v
  ext i
  fin_cases i <;>
    simp [gravity,gravityParameters,Gravity.gradient3,Gravity.gradient,hi,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,enorm] <;> ring

def geometric (x : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,0,x 0; 0,0,x 1; x 2,x 3,0]

def geometricRate (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![g 0*x 0+g 1*x 1-u 1, g 1*x 0+g 2*x 1+u 0,
    g 3*x 2+u 1, g 3*x 3-u 0]

theorem geometric_closure (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 4 → ℝ) :
    geometric (geometricRate g u x)=gravity g*geometric x-skew ![u 0,u 1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [geometric,geometricRate,gravity,skew,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

def cartesian (x : Fin 10 → ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  !![x 0,x 2,x 4,x 6,0,0; x 1,x 3,x 5,x 7,0,0; 0,0,0,0,x 8,x 9]

def componentForce (u : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  !![u 0,u 1,0,0,0,0; 0,0,u 0,u 1,0,0; 0,0,0,0,u 0,u 1]

def componentWeights (R : SO3) : Fin 6 → ℝ :=
  ![R.val 0 0-1,R.val 0 1,R.val 1 0,R.val 1 1-1,R.val 2 0,R.val 2 1]

/-- Six force columns retain the exact finite rotation for planar thrust. -/
theorem component_forcing (R : SO3) (u : Fin 2 → ℝ) :
    componentForce u *ᵥ componentWeights R =
      rotate R ![u 0,u 1,0]-![u 0,u 1,0] := by
  ext i
  fin_cases i <;>
    simp [componentForce,componentWeights,rotate,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

def cartesianRate (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 10 → ℝ) : Fin 10 → ℝ :=
  ![g 0*x 0+g 1*x 1+u 0, g 1*x 0+g 2*x 1,
    g 0*x 2+g 1*x 3+u 1, g 1*x 2+g 2*x 3,
    g 0*x 4+g 1*x 5, g 1*x 4+g 2*x 5+u 0,
    g 0*x 6+g 1*x 7, g 1*x 6+g 2*x 7+u 1,
    g 3*x 8+u 0, g 3*x 9+u 1]

theorem cartesian_closure (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 10 → ℝ) :
    cartesian (cartesianRate g u x)=gravity g*cartesian x+componentForce u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartesian,cartesianRate,gravity,componentForce,Matrix.mul_apply,Fin.sum_univ_succ]

/-- The four coefficients needed by the geometric reconstruction can be
propagated directly, without computing the ten Cartesian coefficients. -/
def reduce (x : Fin 10 → ℝ) : Fin 4 → ℝ := ![x 4-x 2,x 5-x 3,x 9,-x 8]

theorem reduction_commutes (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 10 → ℝ) :
    reduce (cartesianRate g u x)=geometricRate g u (reduce x) := by
  ext i
  fin_cases i <;> simp [reduce,geometricRate,cartesianRate] <;> ring

open Planning.FlopKernel

private def dot2 (a b x y : ℝ) : Value ℝ := add (mul (input a) (input x)) (mul (input b) (input y))
private def driven (a b x y f : ℝ) : Value ℝ := add (dot2 a b x y) (input f)
private def normal (a x f : ℝ) : Value ℝ := add (mul (input a) (input x)) (input f)

def geometricKernel (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Value ℝ :=
  ![driven (g 0) (g 1) (x 0) (x 1) (-u 1), driven (g 1) (g 2) (x 0) (x 1) (u 0),
    normal (g 3) (x 2) (u 1), normal (g 3) (x 3) (-u 0)]

def cartesianKernel (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 10 → ℝ) : Fin 10 → Value ℝ :=
  ![driven (g 0) (g 1) (x 0) (x 1) (u 0), dot2 (g 1) (g 2) (x 0) (x 1),
    driven (g 0) (g 1) (x 2) (x 3) (u 1), dot2 (g 1) (g 2) (x 2) (x 3),
    dot2 (g 0) (g 1) (x 4) (x 5), driven (g 1) (g 2) (x 4) (x 5) (u 0),
    dot2 (g 0) (g 1) (x 6) (x 7), driven (g 1) (g 2) (x 6) (x 7) (u 1),
    normal (g 3) (x 8) (u 0), normal (g 3) (x 9) (u 1)]

theorem geometric_kernel_value (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 4 → ℝ) :
    (fun i => (geometricKernel g u x i).value)=geometricRate g u x := by
  ext i
  fin_cases i <;> simp [geometricKernel,geometricRate,driven,dot2,normal,
    Planning.FlopKernel.add,Planning.FlopKernel.mul,input,sub_eq_add_neg]

theorem cartesian_kernel_value (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 10 → ℝ) :
    (fun i => (cartesianKernel g u x i).value)=cartesianRate g u x := by
  ext i
  fin_cases i <;> rfl

/-- Assigning p'=v uses no arithmetic. Negating the two known force inputs
is separate, as in the common operation model. No IEEE claim is made. -/
theorem kernel_work (g : Fin 4 → ℝ) (u : Fin 2 → ℝ) (x : Fin 4 → ℝ) (y : Fin 10 → ℝ) :
    (∑ i : Fin 4, (geometricKernel g u x i).flops)=12 ∧
    (∑ i : Fin 10, (cartesianKernel g u y i).flops)=32 := by
  norm_num [geometricKernel,cartesianKernel,driven,dot2,normal,
    Planning.FlopKernel.add,Planning.FlopKernel.mul,input,Fin.sum_univ_succ]

end GNC.PlanarResponseReduction
