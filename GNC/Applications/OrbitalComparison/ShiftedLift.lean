import Mathlib.Analysis.Calculus.Deriv.Add
import GNC.Analysis.CirclePolynomial
import GNC.Dynamics.CircularRendezvous
import Mathlib.Tactic

/-! Exact candidate subtraction for the rotating five-state inverse-radius
lift. A validated integrator can propagate these error equations instead of
subtracting two large flow enclosures. The differential defect is retained.
This proves the change of variables, not correctness of an external solver.
-/
noncomputable section
namespace GNC.OrbitalComparison.ShiftedLift

abbrev State := Fin 5 → ℝ

/-- Sound polynomial parameter enclosure. The full box contains extra
off-circle points, which may increase an enclosure but cannot exclude any
admissible constant pointing angle. -/
theorem parameter_box {θ a : ℝ} (ha : |θ| ≤ a) :
    |Real.sin θ| ≤ a ∧ 0 ≤ 1-Real.cos θ ∧ 1-Real.cos θ ≤ a^2/2 ∧
      (Real.sin θ)^2 = 2*(1-Real.cos θ)-(1-Real.cos θ)^2 := by
  have hsin := (Real.abs_sin_le_abs (x := θ)).trans ha
  have hc := Real.cos_le_one θ
  have hcos := CirclePolynomial.cosine_bound θ
  rw [abs_of_nonneg (sub_nonneg.mpr hc)] at hcos
  have hsq : θ^2 ≤ a^2 := by
    have h0 := abs_nonneg θ
    nlinarith [sq_abs θ]
  have htrig' := Real.sin_sq_add_cos_sq θ
  refine ⟨hsin, by linarith, ?_, ?_⟩ <;> nlinarith

theorem mission_parameter_box {θ : ℝ} (ha : |θ| ≤ 7/20) :
    |Real.sin θ| ≤ 7/20 ∧ 0 ≤ 1-Real.cos θ ∧ 1-Real.cos θ ≤ 49/800 ∧
      (Real.sin θ)^2 = 2*(1-Real.cos θ)-(1-Real.cos θ)^2 := by
  convert parameter_box ha using 1
  norm_num

/-- An outward-rounded step covers the requested horizon without restricting
the comparator to a power-of-two step count. The solver must propagate the
entire rounded interval; no endpoint error allowance is substituted. -/
theorem step_horizon {n : ℕ} {h : ℝ} (hn : 0 < n) (hh : 1/(n:ℝ) ≤ h) :
    1 ≤ (n:ℝ)*h := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have := (div_le_iff₀ hn').mp hh
  nlinarith

def field (w k fx fy : ℝ) (z : State) : State :=
  ![z 2 + w*z 1, z 3-w*z 0,
    w*z 3-k*((1+z 0)*(1+z 4)^3-1)+fx,
    -w*z 2-k*z 1*(1+z 4)^3+fy,
    -(1+z 4)^3*((1+z 0)*z 2+z 1*z 3+w*z 1)]

abbrev radius := CircularRendezvous.radius

/-- Physical inverse-square rate with the inertial velocity difference
expressed in rotating axes; w and k are independently normalized constants. -/
def physicalRate (w k fx fy : ℝ) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![z 2+w*z 1, z 3-w*z 0,
    w*z 3-k*((1+z 0)/(radius z)^3-1)+fx,
    -w*z 2-k*z 1/(radius z)^3+fy]

def lift (z : Fin 4 → ℝ) : State :=
  ![z 0,z 1,z 2,z 3,(radius z)⁻¹-1]

/-- The extra inverse-radius state obeys the polynomial ODE exactly;
no gravity Taylor approximation is introduced by the lift. -/
theorem physical_lift_derivative {X : ℝ → Fin 4 → ℝ} {w k fx fy t : ℝ}
    (hX : HasDerivAt X (physicalRate w k fx fy (X t)) t)
    (hr : 0 < radius (X t)) :
    HasDerivAt (fun s => lift (X s)) (field w k fx fy (lift (X t))) t := by
  have h0 := hasDerivAt_pi.mp hX 0
  have h1 := hasDerivAt_pi.mp hX 1
  have h2 := hasDerivAt_pi.mp hX 2
  have h3 := hasDerivAt_pi.mp hX 3
  simp only [physicalRate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  have hs : (1+X t 0)^2+X t 1^2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mp hr)
  have hinv := (((((h0.const_add 1).pow 2).add (h1.pow 2)).sqrt hs).inv
    (ne_of_gt hr)).sub_const 1
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift,field] using h0
  · simpa [lift,field] using h1
  · convert h2 using 1
    simp [field,lift,div_eq_mul_inv]
  · convert h3 using 1
    simp [field,lift,div_eq_mul_inv]
  · convert hinv using 1
    simp [field,lift,radius,CircularRendezvous.radius]
    field_simp
    <;> ring

def cubeDifference (p e : ℝ) : ℝ :=
  e*(3*(1+p)^2+3*(1+p)*e+e^2)

def radialDifference (w : ℝ) (p e : State) : ℝ :=
  (1+p 0)*e 2+p 2*e 0+e 0*e 2+
    p 1*e 3+p 3*e 1+e 1*e 3+w*e 1

def perturbation (w k : ℝ) (p e : State) : State :=
  let g := (1+p 4)^3
  let dg := cubeDifference (p 4) (e 4)
  let q := (1+p 0)*p 2+p 1*p 3+w*p 1
  let dq := radialDifference w p e
  ![e 2+w*e 1, e 3-w*e 0,
    w*e 3-k*(g*e 0+(1+p 0)*dg+e 0*dg),
    -w*e 2-k*(g*e 1+p 1*dg+e 1*dg),
    -(g*dq+q*dg+dg*dq)]

theorem perturbation_eq (w k fx fy : ℝ) (p e : State) :
    perturbation w k p e = field w k fx fy (p+e)-field w k fx fy p := by
  funext i
  fin_cases i <;>
    simp [perturbation, field, cubeDifference, radialDifference, Pi.add_apply,
      Pi.sub_apply] <;> ring

theorem shifted_derivative (w k fx fy : ℝ) (X P : ℝ → State)
    (dP : State) (t : ℝ)
    (hX : HasDerivAt X (field w k fx fy (X t)) t)
    (hP : HasDerivAt P dP t) :
    HasDerivAt (fun s => X s-P s)
      (perturbation w k (P t) (X t-P t)+(field w k fx fy (P t)-dP)) t := by
  rw [perturbation_eq w k fx fy]
  have hcancel : P t+(X t-P t) = X t := by abel
  rw [hcancel]
  convert hX.sub hP using 1
  module

theorem reconstructed_derivative (w k fx fy : ℝ) (E P : ℝ → State)
    (dP : State) (t : ℝ)
    (hE : HasDerivAt E
      (perturbation w k (P t) (E t)+(field w k fx fy (P t)-dP)) t)
    (hP : HasDerivAt P dP t) :
    HasDerivAt (fun s => P s+E s) (field w k fx fy (P t+E t)) t := by
  rw [perturbation_eq w k fx fy] at hE
  convert hP.add hE using 1
  module

end GNC.OrbitalComparison.ShiftedLift
