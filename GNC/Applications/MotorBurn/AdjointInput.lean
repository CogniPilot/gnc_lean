import GNC.Applications.MotorBurn.Specification
import GNC.Analysis.PolynomialAdjointChain
import GNC.Control.PointingCylinder
import GNC.Control.ControllerThrust

/-! Directional support for the motor benchmark's three-dimensional pointing
disturbance. The reference thrust is along +RTN along-track, with zero common
fixed pointing bias. This is an outer cylinder for a unit pointing cap.
-/
namespace GNC.MotorBurn
open ParametricBox Matrix Set

def accelerationBound : ℚ := forceCommand*(6/5)
def transverseRadius : ℚ := 1/100
def axialLoss : ℚ := 1/20000

def transversePolynomial {C : Type} (A : Model C) (ell : Fin 13 → C) : C :=
  A.add (A.multiply (ell 3) (ell 3)) (A.multiply (ell 5) (ell 5))

def cylinderSupport {C : Type} (A : Model C) (ell : Fin 13 → C)
    (h a L : ℚ) : ℚ :=
  accelerationBound*(transverseRadius*L+axialLoss*A.bound (ell 4) h a)

noncomputable section

@[simp] theorem inputLift_zero : inputLift (0 : Vec3) = 0 := by
  ext i
  fin_cases i <;> rfl

def Cylinder (w : Vec3) : Prop :=
  w 0^2+w 2^2 ≤ ((accelerationBound*transverseRadius : ℚ) : ℝ)^2 ∧
    |w 1| ≤ ((accelerationBound*axialLoss : ℚ) : ℝ)

theorem cylinder_box {w : Vec3} (hw : Cylinder w) (i : Fin 13) :
    |inputLift w i| ≤ (if i.val = 3 ∨ i.val = 4 ∨ i.val = 5
      then (inputMagnitude : ℝ) else 0) := by
  have hb : (0 : ℝ) ≤ (inputMagnitude : ℝ) := by
    norm_num [inputMagnitude, forceCommand]
  have hr : ((accelerationBound*transverseRadius : ℚ) : ℝ) = inputMagnitude := by
    norm_num [accelerationBound, transverseRadius, inputMagnitude]
  have hw0 := hw.1
  rw [hr] at hw0
  have h0 : |w 0| ≤ (inputMagnitude : ℝ) :=
    abs_le_of_sq_le_sq (by nlinarith [hw0, sq_nonneg (w 2)]) hb
  have h2 : |w 2| ≤ (inputMagnitude : ℝ) :=
    abs_le_of_sq_le_sq (by nlinarith [hw0, sq_nonneg (w 0)]) hb
  have h1 : |w 1| ≤ (inputMagnitude : ℝ) := hw.2.trans (by
    norm_num [accelerationBound, axialLoss, inputMagnitude, forceCommand])
  fin_cases i <;> simp_all [inputLift]

/-- Physical pointing and any bounded varying acceleration produce the
declared cylinder. The rational 0.01 radius is proved to enclose the cap.
-/
theorem cap_cylinder (q : Vec3) {a : ℝ}
    (hq : q ∈ ThrustSupport.Cap ![0,1,0] (1-(axialLoss : ℝ)))
    (ha : 0 ≤ a) (hB : a ≤ (accelerationBound : ℝ)) :
    Cylinder (a • (q-![0,1,0])) := by
  have h := ThrustSupport.scaled_coordinate_cylinder q (tau := (transverseRadius : ℝ)) hq
    (by norm_num [axialLoss]) (by norm_num [axialLoss])
    (by norm_num [transverseRadius])
    (by norm_num [axialLoss, transverseRadius]) ha hB
  simpa [Cylinder, Pi.smul_apply, Pi.sub_apply] using h

theorem controller_cylinder (q z : Vec3) {a : ℝ}
    (hV : LogBackstepping.rateStorage 1 q z ≤ (axialLoss : ℝ))
    (ha : 0 ≤ a) (hB : a ≤ (accelerationBound : ℝ)) :
    Cylinder (a • (rotate (rotationExp q) ![0,1,0]-![0,1,0])) := by
  apply cap_cylinder _ _ ha hB
  simpa using LogBackstepping.rateStorage_cap q z ![0,1,0]
    (by norm_num : (0 : ℝ) < 1) (by norm_num [dotProduct, Fin.sum_univ_succ]) hV

theorem cylinder_pair_bound {C : Type} (A : Model C) (ell : Fin 13 → C)
    {h a L : ℚ} {t θ : ℝ} (ht : |t| ≤ (h : ℝ)) (hθ : |θ| ≤ (a : ℝ))
    (hL : 0 ≤ L) (hcheck : A.bound (transversePolynomial A ell) h a ≤ L^2)
    (w : Vec3) (hw : Cylinder w) :
    |∑ i, A.value (ell i) t θ*inputLift w i| ≤
      (cylinderSupport A ell h a L : ℝ) := by
  have hr : (A.value (ell 3) t θ)^2+(A.value (ell 5) t θ)^2 ≤ (L : ℝ)^2 := by
    have hb := (le_abs_self _).trans (A.bound_sound (transversePolynomial A ell) ht hθ)
    have hc : (A.bound (transversePolynomial A ell) h a : ℝ) ≤ (L : ℝ)^2 := by
      exact_mod_cast hcheck
    simpa only [transversePolynomial, A.value_add, A.value_multiply, ← pow_two] using hb.trans hc
  have hp := ThrustSupport.transverse_pair_bound (by exact_mod_cast hL)
    (by norm_num [accelerationBound, transverseRadius, forceCommand] :
      (0 : ℝ) ≤ ((accelerationBound*transverseRadius : ℚ) : ℝ)) hr hw.1
  have hb := A.bound_sound (ell 4) ht hθ
  have ha : |A.value (ell 4) t θ*w 1| ≤
      (A.bound (ell 4) h a : ℝ)*((accelerationBound*axialLoss : ℚ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hb hw.2 (abs_nonneg _) ((abs_nonneg _).trans hb)
  have he : (∑ i, A.value (ell i) t θ*inputLift w i) =
      (A.value (ell 3) t θ*w 0+A.value (ell 5) t θ*w 2)+A.value (ell 4) t θ*w 1 := by
    simp [inputLift, Fin.sum_univ_succ]
    ring
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add hp ha).trans ?_)
  simp only [cylinderSupport, Rat.cast_mul, Rat.cast_add]
  ring_nf
  exact le_rfl

end
end GNC.MotorBurn
