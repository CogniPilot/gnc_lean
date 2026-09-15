import GNC.Dynamics.PolynomialOrbit

/-! Exact planar rotating-frame rendezvous equations about a circular chief.
Length is scaled by the chief radius and time by inverse mean motion. The
origin is the chief, so equal orbital radii alone do not imply rendezvous.
The inverse-radius lift is exact, not a truncated gravity model.
-/
noncomputable section
namespace GNC.CircularRendezvous
open PolynomialODE

def radius (w : Fin 4 → ℝ) : ℝ := Real.sqrt ((1+w 0)^2+w 1^2)

def physicalRate (ar aT : ℝ) (w : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![w 2,w 3,2*w 3+1+w 0-(1+w 0)/(radius w)^3+ar,
    -2*w 2+w 1-w 1/(radius w)^3+aT]

def rate (ar aT : ℝ) (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![z 2,z 3,2*z 3+1+z 0-(1+z 0)*z 4^3+ar,
    -2*z 2+z 1-z 1*z 4^3+aT,-z 4^3*((1+z 0)*z 2+z 1*z 3)]

def lift (w : Fin 4 → ℝ) : Fin 5 → ℝ :=
  ![w 0,w 1,w 2,w 3,(radius w)⁻¹]

theorem lift_continuous {w : ℝ → Fin 4 → ℝ} (hw : Continuous w)
    (hr : ∀ t, 0 < radius (w t)) : Continuous (fun t => lift (w t)) := by
  have hc : Continuous (fun t => radius (w t)) := by unfold radius; fun_prop
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t => w t 0)
    exact (continuous_apply 0).comp hw
  · change Continuous (fun t => w t 1)
    exact (continuous_apply 1).comp hw
  · change Continuous (fun t => w t 2)
    exact (continuous_apply 2).comp hw
  · change Continuous (fun t => w t 3)
    exact (continuous_apply 3).comp hw
  · change Continuous (fun t => (radius (w t))⁻¹)
    exact hc.inv₀ (fun t => ne_of_gt (hr t))

/-- Give the conventional evaluator the same cancellation-free algebra.
The shifted inverse radius eta=1/rho-1 avoids subtracting order-one terms. -/
theorem centered_acceleration (x y vx vy eta ar aT : ℝ) :
    2*vy+1+x-(1+x)*(1+eta)^3+ar =
      2*vy-(1+x)*(3*eta+3*eta^2+eta^3)+ar ∧
    -2*vx+y-y*(1+eta)^3+aT = -2*vx-y*(3*eta+3*eta^2+eta^3)+aT := by
  constructor <;> ring

/-- Actual inverse-square equations lift to a polynomial ODE, including
arbitrary radial/tangential acceleration values on each burn arc. -/
theorem lift_derivative {w : ℝ → Fin 4 → ℝ} {ar aT t : ℝ}
    (hw : HasDerivAt w (physicalRate ar aT (w t)) t) (hr : 0 < radius (w t)) :
    HasDerivAt (fun s => lift (w s)) (rate ar aT (lift (w t))) t := by
  have h0 := hasDerivAt_pi.mp hw 0
  have h1 := hasDerivAt_pi.mp hw 1
  have h2 := hasDerivAt_pi.mp hw 2
  have h3 := hasDerivAt_pi.mp hw 3
  simp only [physicalRate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  have hs : (1+w t 0)^2+w t 1^2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mp hr)
  have hinv := ((((h0.const_add 1).pow 2).add (h1.pow 2)).sqrt hs).inv (ne_of_gt hr)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift,rate] using h0
  · simpa [lift,rate] using h1
  · convert h2 using 1
    simp [rate,lift,div_eq_mul_inv]
  · convert h3 using 1
    simp [rate,lift,div_eq_mul_inv]
  · convert hinv using 1
    simp [rate,lift,radius]
    field_simp
    <;> ring

/-- Polynomial syntax used by the rational certificate checker. -/
def field (ar aT : ℚ) : Fin 5 → Expr 5 :=
  let x := Expr.var 0
  let y := Expr.var 1
  let vx := Expr.var 2
  let vy := Expr.var 3
  let ir := Expr.var 4
  let r := (Expr.constant 1).add x
  let ir3 := ir.multiply (ir.multiply ir)
  ![vx,vy,
    (((Expr.constant 2).multiply vy).add r).add
      ((r.multiply ir3).negate) |>.add (.constant ar),
    ((((Expr.constant (-2)).multiply vx).add y).add
      ((y.multiply ir3).negate)).add (.constant aT),
    (ir3.multiply ((r.multiply vx).add (y.multiply vy))).negate]

theorem field_correct (ar aT : ℚ) (z : Fin 5 → ℝ) (i : Fin 5) :
    (field ar aT i).value z = rate ar aT z i := by
  fin_cases i <;> simp [field,Expr.value,rate] <;> ring_nf <;> simp

/-- Components of inertial velocity difference expressed in the rotating
axes. The rotating derivative alone would omit these position terms. -/
def inertialVelocity (w : Fin 4 → ℝ) : Fin 2 → ℝ := ![w 2-w 1,w 3+w 0]

theorem rendezvous_iff (w : Fin 4 → ℝ) :
    (w 0 = 0 ∧ w 1 = 0 ∧ inertialVelocity w = 0) ↔ w = 0 := by
  constructor
  · rintro ⟨h0,h1,hv⟩
    have h2 := congrFun hv 0
    have h3 := congrFun hv 1
    simp [inertialVelocity,h0,h1] at h2 h3
    ext i
    fin_cases i <;> simp [h0,h1,h2,h3]
  · rintro rfl
    simp [inertialVelocity]

end GNC.CircularRendezvous
