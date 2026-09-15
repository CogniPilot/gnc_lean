import GNC.Applications.OrbitalComparison.ShiftedLift

/-! Exact inertial three-dimensional inverse-radius lift and candidate error
equations used by the spatial external-validator comparison. The force may
depend on time: the derivative statements use its value at the instant in
question. No gravity linearization or omitted inverse-radius defect is used.
These are mathematical identities, not a verification of the C++ evaluator. -/
noncomputable section
namespace GNC.OrbitalComparison.SpatialShiftedLift

abbrev State := Fin 7 → ℝ

def radius (z : Fin 6 → ℝ) : ℝ := Real.sqrt (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2)

def physicalRate (k fx fy fz : ℝ) (z : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![z 3, z 4, z 5, -k*z 0/(radius z)^3+fx,
    -k*z 1/(radius z)^3+fy, -k*z 2/(radius z)^3+fz]

def lift (z : Fin 6 → ℝ) : State :=
  ![z 0,z 1,z 2,z 3,z 4,z 5,(radius z)⁻¹]

def field (k fx fy fz : ℝ) (z : State) : State :=
  ![z 3,z 4,z 5,-k*z 6^3*z 0+fx,-k*z 6^3*z 1+fy,-k*z 6^3*z 2+fz,
    -z 6^3*(z 0*z 3+z 1*z 4+z 2*z 5)]

theorem physical_lift_derivative {X : ℝ → Fin 6 → ℝ} {k fx fy fz t : ℝ}
    (hX : HasDerivAt X (physicalRate k fx fy fz (X t)) t)
    (hr : 0 < radius (X t)) :
    HasDerivAt (fun s => lift (X s)) (field k fx fy fz (lift (X t))) t := by
  have h0 := hasDerivAt_pi.mp hX 0
  have h1 := hasDerivAt_pi.mp hX 1
  have h2 := hasDerivAt_pi.mp hX 2
  have h3 := hasDerivAt_pi.mp hX 3
  have h4 := hasDerivAt_pi.mp hX 4
  have h5 := hasDerivAt_pi.mp hX 5
  simp only [physicalRate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val] at h0 h1 h2 h3 h4 h5
  have hs : X t 0^2+X t 1^2+X t 2^2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mp hr)
  have hinv := (((((h0.pow 2).add (h1.pow 2)).add (h2.pow 2)).sqrt hs).inv
    (ne_of_gt hr))
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [lift,field] using h0
  · simpa [lift,field] using h1
  · simpa [lift,field] using h2
  · convert h3 using 1
    simp [field,lift,div_eq_mul_inv]; ring
  · convert h4 using 1
    simp [field,lift,div_eq_mul_inv]; ring
  · convert h5 using 1
    simp [field,lift,div_eq_mul_inv]; ring
  · convert hinv using 1
    simp [field,lift,radius]
    field_simp

def cubeDifference (p e : ℝ) : ℝ := e*(3*p^2+3*p*e+e^2)

def radialDifference (p e : State) : ℝ :=
  p 0*e 3+p 3*e 0+e 0*e 3+
  p 1*e 4+p 4*e 1+e 1*e 4+
  p 2*e 5+p 5*e 2+e 2*e 5

def perturbation (k : ℝ) (p e : State) : State :=
  let g := p 6^3
  let dg := cubeDifference (p 6) (e 6)
  let q := p 0*p 3+p 1*p 4+p 2*p 5
  let dq := radialDifference p e
  ![e 3,e 4,e 5,-k*(g*e 0+p 0*dg+e 0*dg),
    -k*(g*e 1+p 1*dg+e 1*dg),-k*(g*e 2+p 2*dg+e 2*dg),
    -(g*dq+q*dg+dg*dq)]

theorem perturbation_eq (k fx fy fz : ℝ) (p e : State) :
    perturbation k p e = field k fx fy fz (p+e)-field k fx fy fz p := by
  funext i
  fin_cases i <;> simp [perturbation,field,cubeDifference,radialDifference,
    Pi.add_apply,Pi.sub_apply] <;> ring

theorem shifted_derivative (k fx fy fz : ℝ) (X P : ℝ → State)
    (dP : State) (t : ℝ)
    (hX : HasDerivAt X (field k fx fy fz (X t)) t)
    (hP : HasDerivAt P dP t) :
    HasDerivAt (fun s => X s-P s)
      (perturbation k (P t) (X t-P t)+(field k fx fy fz (P t)-dP)) t := by
  rw [perturbation_eq k fx fy fz]
  have hc : P t+(X t-P t) = X t := by abel
  rw [hc]
  convert hX.sub hP using 1
  module

theorem reconstructed_derivative (k fx fy fz : ℝ) (E P : ℝ → State)
    (dP : State) (t : ℝ)
    (hE : HasDerivAt E
      (perturbation k (P t) (E t)+(field k fx fy fz (P t)-dP)) t)
    (hP : HasDerivAt P dP t) :
    HasDerivAt (fun s => P s+E s) (field k fx fy fz (P t+E t)) t := by
  rw [perturbation_eq k fx fy fz] at hE
  convert hP.add hE using 1
  module

end GNC.OrbitalComparison.SpatialShiftedLift
