import GNC.Applications.ApproachGate.Invariant
import GNC.Analysis.EuclideanBox
import GNC.Analysis.TrigonometricPolynomial
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fixed requirements for a synthetic stand-off rendezvous gate.
The exact commands and proof records are supplied separately. This is an
arrival certificate for the declared model, not a docking or flight approval.
-/
namespace GNC.ApproachGate
open ParametricBox PolynomialODE Matrix

def angle : ℚ := 11/630
def stepDuration : ℚ := 1/20
def initialState (i : Fin 6) : ℚ :=
  if i.val = 0 then -2/196000001 else if i.val = 1 then -28000/196000001 else 0
def gateState : Fin 6 → ℚ := ![-2/784000001,-56000/784000001,0,0,0,0]
def radiusSI : ℚ := 7000000
def speedSquaredSI : ℚ := 398600441800000/7000000

def initialCircle : Fin 11 → CirclePolynomial.Coefficients :=
  ![⟨[[-2/196000001]],[]⟩,⟨[[-28000/196000001]],[]⟩,
    ⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,⟨[],[]⟩,
    ⟨[],[[1]]⟩,⟨[[0,1]],[]⟩,⟨[[1]],[]⟩,⟨[],[]⟩]

def initialPolynomial (i : Fin 11) : BivariatePolynomial.Coefficients :=
  if i.val = 7 then [TrigonometricPolynomial.sine]
  else if i.val = 8 then BivariatePolynomial.subtract [[1]] [TrigonometricPolynomial.cosine]
  else [[if i.val = 0 then -2/196000001 else
    if i.val = 1 then -28000/196000001 else if i.val = 9 then 1 else 0]]

def initialTail (i : Fin 11) : ℚ :=
  if i.val = 7 ∨ i.val = 8 then angle^17/355687428096000 else 0

def positionQuery : Fin 3 → Expr 11 :=
  ![(Expr.var 0).add (.constant (2/784000001)),
    (Expr.var 1).add (.constant (56000/784000001)),.var 2]

def velocityQuery : Fin 3 → Expr 11 :=
  ![(Expr.var 3).add (positionQuery 1).negate,
    (Expr.var 4).add (positionQuery 0),.var 5]

def queryRadius {C : Type} (A : Model C) (s : Step C 11) (e : Expr 11) : ℚ :=
  A.bound (A.atTime (substitute A e s.coefficients) s.duration) 0 s.angle +
    e.differenceMajorant s.region s.error

noncomputable section

theorem one_degree_enclosed {θ : ℝ} (hθ : |θ| ≤ Real.pi/180) :
    |θ| ≤ (angle : ℝ) := by
  norm_num [angle]
  linarith [Real.pi_lt_d4]

theorem initial_radius : CircularRendezvous3D.radius (fun i => (initialState i : ℝ)) = 1 := by
  norm_num [CircularRendezvous3D.radius, initialState]

theorem initial_circle_value (θ t : ℝ) :
    curve circle initialCircle θ t = lift θ 0 (fun i => (initialState i : ℝ)) := by
  simp only [lift, initial_radius]
  ext i
  fin_cases i <;> norm_num [ParametricBox.curve, circle, initialCircle, initialState,
    CirclePolynomial.value, BivariatePolynomial.value, BivariatePolynomial.slice,
    BivariatePolynomial.row, Planning.PolynomialKernel.evaluate]

theorem initial_numbers (θ : ℝ) : inverseDefect (lift θ 0 (fun i => (initialState i : ℝ))) = 0 := by
  change (((CircularRendezvous3D.radius (fun i => (initialState i : ℝ)))⁻¹-1+1)⁻¹)^2 -
    ((1+(initialState 0 : ℝ))^2+(initialState 1 : ℝ)^2+(initialState 2 : ℝ)^2) = 0
  rw [initial_radius]
  norm_num [initialState]

theorem initial_polynomial_error {θ : ℝ} (hθ : |θ| ≤ (angle : ℝ)) (i : Fin 11) :
    |lift θ 0 (fun i => (initialState i : ℝ)) i-
      ParametricBox.curve polynomial initialPolynomial θ 0 i| ≤ (initialTail i : ℝ) := by
  have hb : |θ|^17/355687428096000 ≤ ((angle^17/355687428096000 : ℚ) : ℝ) := by
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 17) (by norm_num)
  simp only [lift, initial_radius]
  fin_cases i
  all_goals first
    | solve | norm_num [ParametricBox.curve, polynomial, initialPolynomial, initialTail,
        initialState, BivariatePolynomial.value, BivariatePolynomial.slice,
        BivariatePolynomial.row, Planning.PolynomialKernel.evaluate]
    | skip
  · change |Real.sin θ-BivariatePolynomial.value [TrigonometricPolynomial.sine] 0 θ| ≤ _
    simpa [initialTail, BivariatePolynomial.value, BivariatePolynomial.slice,
      Planning.PolynomialKernel.evaluate] using (TrigonometricPolynomial.sine_bound θ).trans hb
  · change |1-Real.cos θ-BivariatePolynomial.value
        (BivariatePolynomial.subtract [[1]] [TrigonometricPolynomial.cosine]) 0 θ| ≤ _
    rw [BivariatePolynomial.value_subtract]
    have hv : BivariatePolynomial.value [[1]] (0 : ℝ) θ = 1 := by
      norm_num [BivariatePolynomial.value, BivariatePolynomial.slice,
        BivariatePolynomial.row, Planning.PolynomialKernel.evaluate]
    rw [hv]
    have hv' : BivariatePolynomial.value [TrigonometricPolynomial.cosine] (0 : ℝ) θ =
        BivariatePolynomial.row TrigonometricPolynomial.cosine θ := by
      simp [BivariatePolynomial.value, BivariatePolynomial.slice, Planning.PolynomialKernel.evaluate]
    rw [hv']
    rw [show 1-Real.cos θ-(1-BivariatePolynomial.row TrigonometricPolynomial.cosine θ) =
      -(Real.cos θ-BivariatePolynomial.row TrigonometricPolynomial.cosine θ) by ring, abs_neg]
    exact (TrigonometricPolynomial.cosine_bound θ).trans hb

def positionError (z : Fin 11 → ℝ) : Vec3 :=
  ![z 0-(gateState 0 : ℝ),z 1-(gateState 1 : ℝ),z 2]

def velocityError (z : Fin 11 → ℝ) : Vec3 :=
  ![z 3-(z 1-(gateState 1 : ℝ)),z 4+(z 0-(gateState 0 : ℝ)),z 5]

theorem position_query_value (z : Fin 11 → ℝ) (i : Fin 3) :
    (positionQuery i).value z = positionError z i := by
  fin_cases i <;> norm_num [positionQuery, Expr.value, positionError, gateState] <;> ring

theorem velocity_query_value (z : Fin 11 → ℝ) (i : Fin 3) :
    (velocityQuery i).value z = velocityError z i := by
  fin_cases i <;> norm_num [velocityQuery, positionQuery, Expr.value, velocityError, gateState] <;> ring

theorem terminal_norms {C : Type} (A : Model C) (s : Step C 11)
    (f : Fin 11 → Expr 11) (hs : s.Valid A f)
    (P V : ℚ) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hp : radiusSI^2 * (∑ i, (queryRadius A s (positionQuery i))^2) ≤ P^2)
    (hv : speedSquaredSI * (∑ i, (queryRadius A s (velocityQuery i))^2) ≤ V^2)
    {θ : ℝ} (hθ : |θ| ≤ (s.angle : ℝ)) (z : Fin 11 → ℝ)
    (hz : ∀ i, |z i-curve A s.coefficients θ s.duration i| ≤ (s.error i : ℝ)) :
    enorm ((radiusSI : ℝ) • positionError z) ≤ (P : ℝ) ∧
    enorm (Real.sqrt (speedSquaredSI : ℝ) • velocityError z) ≤ (V : ℝ) := by
  have hpos (i : Fin 3) : |positionError z i| ≤ (queryRadius A s (positionQuery i) : ℝ) := by
    simpa only [position_query_value] using terminal_query A s f hs (positionQuery i) hθ z hz
  have hvel (i : Fin 3) : |velocityError z i| ≤ (queryRadius A s (velocityQuery i) : ℝ) := by
    simpa only [velocity_query_value] using terminal_query A s f hs (velocityQuery i) hθ z hz
  have hR : (0 : ℝ) ≤ radiusSI := by norm_num [radiusSI]
  have hS : (0 : ℝ) ≤ speedSquaredSI := by norm_num [speedSquaredSI]
  constructor
  · apply enorm_le_of_component_bounds _ (fun i => (radiusSI : ℝ)*queryRadius A s (positionQuery i))
    · intro i
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hR] using
        mul_le_mul_of_nonneg_left (hpos i) hR
    · exact_mod_cast hP
    · have hh : (radiusSI : ℝ)^2*(∑ i, (queryRadius A s (positionQuery i) : ℝ)^2) ≤ (P : ℝ)^2 := by
        exact_mod_cast hp
      simpa only [mul_pow, ← Finset.mul_sum] using hh
  · apply enorm_le_of_component_bounds _
      (fun i => Real.sqrt (speedSquaredSI : ℝ)*queryRadius A s (velocityQuery i))
    · intro i
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
        mul_le_mul_of_nonneg_left (hvel i) (Real.sqrt_nonneg _)
    · exact_mod_cast hV
    · have hh : (speedSquaredSI : ℝ)*(∑ i, (queryRadius A s (velocityQuery i) : ℝ)^2) ≤ (V : ℝ)^2 := by
        exact_mod_cast hv
      simpa only [mul_pow, Real.sq_sqrt hS, ← Finset.mul_sum] using hh

end
end GNC.ApproachGate
