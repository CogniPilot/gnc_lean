import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! A concrete ideal aerodynamic allocation for the planar reference.
Following Lévine Chapter 14, force inversion is a distinct obligation.
Here lift is K*α and drag is independent of α at fixed speed; A is drag
plus desired tangential inertial force. This is an explicit ideal model.
-/
noncomputable section
open Real Set Matrix
namespace GNC.FixedWingAllocation

def liftEquation (K A α : ℝ) : ℝ := K*α+A*tan α

/-- A unique feasible angle-of-attack branch for the ideal force inversion.
The interval, sign, and load hypotheses are explicit and quantitatively usable. -/
theorem exists_unique_angle {K A L αmax : ℝ}
    (hK : 0 < K) (hA : 0 ≤ A) (hL : 0 < L)
    (hα : 0 < αmax) (hαπ : αmax < π/2) (hload : L ≤ K*αmax) :
    ∃! α : ℝ, α ∈ Icc 0 αmax ∧ liftEquation K A α = L := by
  have hsub : Icc (0:ℝ) αmax ⊆ Ioo (-(π/2)) (π/2) := by
    intro x hx
    exact ⟨by linarith [pi_pos, hx.1], hx.2.trans_lt hαπ⟩
  have hc : ContinuousOn (liftEquation K A) (Icc 0 αmax) :=
    (continuous_const.mul continuous_id).continuousOn.add
      (continuousOn_const.mul (continuousOn_tan_Ioo.mono hsub))
  have hmono : StrictMonoOn (liftEquation K A) (Icc 0 αmax) := by
    intro x hx y hy hxy
    have ht := (strictMonoOn_tan (hsub hx) (hsub hy) hxy).le
    have hmul := mul_le_mul_of_nonneg_left ht hA
    dsimp [liftEquation]
    nlinarith [mul_pos hK (sub_pos.mpr hxy)]
  have hend : L ≤ liftEquation K A αmax := by
    have ht := tan_nonneg_of_nonneg_of_le_pi_div_two hα.le hαπ.le
    dsimp [liftEquation]
    nlinarith [mul_nonneg hA ht]
  obtain ⟨α, hmem, heq⟩ := intermediate_value_Icc hα.le hc
    (show L ∈ Icc (liftEquation K A 0) (liftEquation K A αmax) by
      exact ⟨by simpa [liftEquation] using hL.le, hend⟩)
  refine ⟨α, ⟨hmem, heq⟩, ?_⟩
  intro β hβ
  exact hmono.injOn hβ.1 hmem (hβ.2.trans heq.symm)

/-- Thrust and linear lift satisfy the required longitudinal and normal force
balances at the allocated angle. The cosine hypothesis follows on the branch. -/
theorem force_balance {K A L α : ℝ} (hc : cos α ≠ 0)
    (he : liftEquation K A α = L) :
    (A/cos α)*cos α = A ∧ K*α+(A/cos α)*sin α = L := by
  constructor
  · field_simp
  · rw [liftEquation, tan_eq_sin_div_cos] at he
    convert he using 1 <;> ring

theorem thrust_nonnegative {A α : ℝ} (hA : 0 ≤ A)
    (hα : α ∈ Ioo (-(π/2)) (π/2)) : 0 ≤ A/cos α :=
  div_nonneg hA (cos_pos_of_mem_Ioo hα).le

def forceMap (K drag : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0*cos (x 1)-drag,
    (K*x 1+x 0*sin (x 1))*sin (x 2),
    -(K*x 1+x 0*sin (x 1))*cos (x 2)]

def forceJacobian (K : ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos (x 1), -x 0*sin (x 1), 0;
     sin (x 1)*sin (x 2), (K+x 0*cos (x 1))*sin (x 2),
       (K*x 1+x 0*sin (x 1))*cos (x 2);
     -sin (x 1)*cos (x 2), -(K+x 0*cos (x 1))*cos (x 2),
       (K*x 1+x 0*sin (x 1))*sin (x 2)]

/-- The proposed force Jacobian is the actual derivative along every
differentiable parameter curve. Parameters are thrust, attack angle, bank. -/
theorem forceMap_derivative (K drag : ℝ) {x : ℝ → Fin 3 → ℝ}
    {dx : Fin 3 → ℝ} {t : ℝ} (hx : HasDerivAt x dx t) :
    HasDerivAt (fun s => forceMap K drag (x s))
      (forceJacobian K (x t) *ᵥ dx) t := by
  have h0 := hasDerivAt_pi.mp hx (0 : Fin 3)
  have h1 := hasDerivAt_pi.mp hx (1 : Fin 3)
  have h2 := hasDerivAt_pi.mp hx (2 : Fin 3)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert ((h0.mul h1.cos).sub_const drag) using 1 <;>
      simp [forceMap, forceJacobian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, vecHead, vecTail] <;> ring
  · convert (((h1.const_mul K).add (h0.mul h1.sin)).mul h2.sin) using 1 <;>
      simp [forceMap, forceJacobian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, vecHead, vecTail] <;> ring
  · convert (((h1.const_mul K).add (h0.mul h1.sin)).neg.mul h2.cos) using 1 <;>
      simp [forceMap, forceJacobian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, vecHead, vecTail] <;> ring

theorem forceJacobian_det (K : ℝ) (x : Fin 3 → ℝ) :
    (forceJacobian K x).det =
      (K*x 1+x 0*sin (x 1))*(K*cos (x 1)+x 0) := by
  calc
    _ = (K*x 1+x 0*sin (x 1))*
      (K*cos (x 1)+x 0*(sin (x 1)^2+cos (x 1)^2))*
      (sin (x 2)^2+cos (x 2)^2) := by
        simp only [forceJacobian, Matrix.det_fin_three]
        change cos (x 1)*((K+x 0*cos (x 1))*sin (x 2))*
          ((K*x 1+x 0*sin (x 1))*sin (x 2)) -
          cos (x 1)*((K*x 1+x 0*sin (x 1))*cos (x 2))*(-(K+x 0*cos (x 1))*cos (x 2)) -
          (-x 0*sin (x 1))*(sin (x 1)*sin (x 2))*((K*x 1+x 0*sin (x 1))*sin (x 2)) +
          (-x 0*sin (x 1))*((K*x 1+x 0*sin (x 1))*cos (x 2))*(-sin (x 1)*cos (x 2)) +
          0*(sin (x 1)*sin (x 2))*(-(K+x 0*cos (x 1))*cos (x 2)) -
          0*((K+x 0*cos (x 1))*sin (x 2))*(-sin (x 1)*cos (x 2)) = _
        ring
    _ = _ := by rw [sin_sq_add_cos_sq, sin_sq_add_cos_sq]; ring

theorem forceJacobian_nonsingular {K : ℝ} {x : Fin 3 → ℝ}
    (hK : 0 < K) (hF : 0 ≤ x 0) (hL : 0 < K*x 1+x 0*sin (x 1))
    (hc : 0 < cos (x 1)) :
    (forceJacobian K x).det ≠ 0 := by
  rw [forceJacobian_det]
  exact ne_of_gt (mul_pos hL (add_pos_of_pos_of_nonneg (mul_pos hK hc) hF))

/-- Coordinated-bank allocation, using the book's Earth z-down convention.
The required total lift/thrust-normal force balances weight and signed
horizontal normal acceleration. -/
theorem bank_balance (m g an : ℝ) (hg : g ≠ 0) :
    let μ := arctan (an/g)
    let L := m*g/cos μ
    L*cos μ = m*g ∧ L*sin μ = m*an := by
  dsimp
  have hc := (cos_arctan_pos (an/g)).ne'
  constructor
  · field_simp
  · have ht : sin (arctan (an/g))/cos (arctan (an/g)) = an/g := by
      rw [← tan_eq_sin_div_cos, tan_arctan]
    calc
      m*g/cos (arctan (an/g))*sin (arctan (an/g)) =
        m*g*(sin (arctan (an/g))/cos (arctan (an/g))) := by ring
      _ = m*an := by rw [ht]; field_simp

end GNC.FixedWingAllocation

/-! Concrete moment allocation used in the six-DOF Modelica experiment.
These certificates concern the stated rational coefficient model and an
unconstrained surface command. They do not certify actuator feasibility,
the coefficient fit, the compiler, or the complete aircraft feedback loop.
-/
namespace GNC.FixedWingAllocation.SportCub

def controlCoefficients : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1/20 : ℝ), 0, 3/500;
     0, 3/10, 0;
     3/500, 0, 3/200]

theorem controlCoefficients_det :
    controlCoefficients.det = 1071/5000000 := by
  rw [controlCoefficients, Matrix.det_fin_three]
  change (1/20 : ℝ)*(3/10)*(3/200) - (1/20)*0*0 - 0*0*(3/200) +
    0*0*(3/500) + (3/500)*0*0 - (3/500)*(3/10)*(3/500) = _
  norm_num

/-- The explicit aileron/elevator/rudder inverse implemented in Modelica. -/
def allocate (b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![((3/200)*b 0-(3/500)*b 2)/((1/20)*(3/200)-(3/500)*(3/500)),
    b 1/(3/10),
    ((1/20)*b 2-(3/500)*b 0)/((1/20)*(3/200)-(3/500)*(3/500))]

theorem allocate_correct (b : Fin 3 → ℝ) :
    controlCoefficients *ᵥ allocate b = b := by
  ext i
  fin_cases i <;>
    norm_num [controlCoefficients, allocate, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vecHead, vecTail] <;> ring <;> rfl

def momentMap (qS span chord : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![qS*span, qS*chord, qS*span] * controlCoefficients

theorem momentMap_det (qS span chord : ℝ) :
    (momentMap qS span chord).det = qS^3*span^2*chord*(1071/5000000) := by
  simp [momentMap, Matrix.det_mul, controlCoefficients_det,
    Matrix.det_diagonal, Fin.prod_univ_succ]
  <;> ring

theorem momentMap_nonsingular {qS span chord : ℝ}
    (hqS : 0 < qS) (hb : 0 < span) (hc : 0 < chord) :
    (momentMap qS span chord).det ≠ 0 := by
  rw [momentMap_det]
  positivity

def inertia : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1/1250 : ℝ), 0, -1/10000;
     0, 3/2500, 0;
     -1/10000, 0, 9/5000]

theorem inertia_det : inertia.det = 429/250000000000 := by
  rw [inertia, Matrix.det_fin_three]
  change (1/1250 : ℝ)*(3/2500)*(9/5000) - (1/1250)*0*0 - 0*0*(9/5000) +
    0*0*(-1/10000) + (-1/10000)*0*0 - (-1/10000)*(3/2500)*(-1/10000) = _
  norm_num

/-- Positive inertia energy, including the cross-inertia sign used in FRD. -/
theorem inertia_energy_positive {w : Fin 3 → ℝ} (hw : w ≠ 0) :
    0 < dotProduct w (inertia *ᵥ w) := by
  have hnonzero : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    ext i
    fin_cases i <;> simp_all
  have identity : dotProduct w (inertia *ᵥ w) =
      (7/10000 : ℝ)*(w 0)^2 + (3/2500)*(w 1)^2 +
      (17/10000)*(w 2)^2 + (1/10000)*(w 0-w 2)^2 := by
    simp [inertia, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  rcases hnonzero with h | h | h <;>
    nlinarith [sq_pos_of_ne_zero h, sq_nonneg (w 0), sq_nonneg (w 1),
      sq_nonneg (w 2), sq_nonneg (w 0-w 2)]

end GNC.FixedWingAllocation.SportCub
